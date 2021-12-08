//use halo2::pasta::pasta::{EqAffine, Point, Scalar,Fp};
use halo2::poly::{
    commitment::{Blind, Params as CParams},
    Polynomial,
};
use group::Curve;
use halo2::{
    transcript::{Blake2bRead, Blake2bWrite, Challenge255, Transcript,EncodedChallenge, TranscriptWrite},
    arithmetic::{eval_polynomial,CurveAffine},
    poly::{multiopen::{self,ProverQuery,VerifierQuery as VQ}, EvaluationDomain, Coeff},
};
use thiserror::Error;
use group::ff::Field;
use std::{fmt::{ Formatter,Debug},io};

pub type Poly<C> = Polynomial<<C as CurveAffine>::ScalarExt, Coeff>;
pub type Domain<C> = EvaluationDomain<C>;

pub struct Params<C: CurveAffine> {
    n: usize, // total length of data
    layers: usize,
    arity: usize,
    k: usize, // 2^k = arity
    domain: Domain<C::ScalarExt>,
    params: CParams<C>,
}

impl<C> Params<C>
where
    C: CurveAffine,
{
    pub fn new(len: usize, arity: usize) -> Result<Self, Error> {
        if !len.is_power_of_two() {
            return Err(Error::NotPowerOfTwo);
        }
        let logn = len.log2() as usize;

        // logb(x) = logc(x) / logc(b)
        // so log_arity(n) = log2(n) / log_2(arity)
        let layers = logn / arity.log2() as usize;
        //let layers = logn / arity as usize;
        let k = arity.log2();
        let domain = EvaluationDomain::new(1, k);
        let params = CParams::new(k);
        println!("len {} arity {} logn {} layers {} k {}",len,arity,logn,layers,k);
        Ok(Self {
            k: k as usize,
            layers,
            n: len,
            arity,
            domain,
            params,
        })
    }

    pub fn poly(&self, data: Vec<C::ScalarExt>) -> Result<Poly<C>, Error> {
         if data.len() != self.arity {
            return Err(Error::InvalidSize);
        }

        // TODO hack halo2 to use lagrange form for everything
        Ok(self.domain.lagrange_to_coeff(self.domain.lagrange_from_vec(data)))
    }

    // commitment use a NULL blind factor -> i.e. it is NOT bliding at the moment,
    // just for simplicity of PoC
    pub fn commitment(&self, p: &Poly<C>) -> C::CurveExt {
        let r = Blind(C::ScalarExt::zero());
        self.params.commit(p, r)
    }

    pub fn build_tree(&self, mut data: Vec<C::ScalarExt>) -> Result<Node<C>, Error> {
        let params = &self;
        if data.len() % params.arity != 0 {
            return Err(Error::InvalidSize);
        }

        let mut layer_nodes = vec![];
        let mut leaf_step = true;
        let mut layer = params.layers;
        while layer > 0 { 
            // this assumes a perfect balanced tree
            let n_nodes = params.arity.pow((layer-1) as u32);
            println!("Build: layer {} (over {}) -> how many nodes {}",layer,params.layers,n_nodes);
            layer_nodes = match (0..n_nodes).map(|_| {
                    if leaf_step {
                        println!("Draining {} nodes from {} data nodes",params.arity,data.len());
                        Node::new_leaf(&params, data.drain(0..params.arity).collect::<Vec<_>>())
                    } else {
                        println!("Draining {} vnodes from {} vnodes",params.arity,layer_nodes.len());
                        Node::new_inode(&params, layer_nodes.drain(0..params.arity).collect::<Vec<_>>())
                    }
                })
                .collect::<Result<Vec<_>,_>>() {
                    Ok(nodes) => nodes,
                    Err(e) => return Err(e),
                };
            leaf_step = leaf_step & false;
            layer -= 1;
            if layer_nodes.len() == 1  {
                break
            }
        }
        Ok(layer_nodes.pop().unwrap())
    }

    

    // we assume no more than 2^64 values being committed...
    pub fn openings(&self, root: &Node<C>, positions: &[u64]) -> io::Result<Proof<C>> {
        let params = &self;
        if positions.len() == 0{
            panic!("wow");
        }
        // find the right node for each position, and keep accumulating the
        // polynomials and commitments along the way
        // TODO: better access for the prover might be better, like random
        // access to all verkle node leaves. In the end it's only a logarithmic
        // number of basic arithmetic, it shouldn't make a huge difference
        let (prover_queries,verifier_queries) :(Vec<ProverQuery<C>>,Vec<VerifierQuery<C>>) =
            positions.iter()
            .map(|pos| 
                prover_recurse(params, *pos,root,true)
            ).flatten().unzip();
            //).flatten().collect::<Vec<_>>();
        //println!("from positions {:?} -> Queries {:?}",positions, queries);
        // TODO see if needs to write other stuff..
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        multiopen::create_proof(&params.params, &mut transcript, prover_queries)?;
        Ok(Proof {
            transcript: transcript.finalize(),
            queries: verifier_queries,
        })
    }
    pub fn verify_proof(&self,mut proof: Proof<C>, root_commit: &C, positions :&[u64]) -> Result<(),Error> {
        let params = &self;
        let length = params.layers - 1;

        // whole reason of that loop before is because I can't drain inside the
        // iterator otherwise there is no owner of the data when creating the
        // verifier query which takes a reference. Anyway to do better than this ?
        let pqueries = positions.iter().map(|_| {
            let mut q = proof.queries.drain(0..length).collect::<Vec<_>>();
            q[0].0 = root_commit.clone(); // the parent is the root
            q
        }).collect::<Vec<_>>();

        let queries = positions.iter().enumerate().map(|(i,pos)| {
            // all the positions in the path from root to leaf
            let path_pos = verifier_recurse(params.arity, *pos);
            //let mut pqueries = proof.queries.drain(0..length).collect::<Vec<_>>();
            //pqueries[0].0 = root_commit.clone();
            // check the hash consistency
            let consistent_hashes = (1..length).all(|j| { 
                // the hash of commitment shoud be the value evaluated the layer
                // above
                let exp = point_to_scalar(&pqueries[i][j].0);
                let got = pqueries[i][j-1].1;
                exp == got
            });
            if !consistent_hashes { 
                return Err(Error::InvalidProof("consistency check failed".to_string()));
            }
            // associate the positions and the queries given by prover
            // we put the root commitment ourself
            Ok(path_pos.into_iter().zip(pqueries[i].iter())
                .map(|(pos,query)| VQ::new_commitment(&query.0,C::ScalarExt::from(pos),query.1)))
        }).map(|i| i.unwrap()).flatten().collect::<Vec<_>>();

        let mut proof_transcript = &proof.transcript[..];
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&mut proof_transcript);
        let msm = self.params.empty_msm();
        match multiopen::verify_proof(&self.params,&mut transcript,queries, msm) {
            Ok(guard) => match guard.use_challenges().eval() { 
                true => Ok(()), 
                false => Err(Error::InvalidProof("final verification failed".to_string())), 
            },
            Err(_) => Err(Error::InvalidProof("final verification failed".to_string())),
        }
    }
}

pub struct Node<C: CurveAffine> {
    commitment: C::CurveExt,
    poly: Poly<C>,
    children: Option<Vec<Node<C>>>,
}

impl<C> Node<C>
where
    C: CurveAffine,
{
    fn new_inode(
        params: &Params<C>,
        children: Vec<Node<C>>,
    ) -> Result<Node<C>, Error> {
        let data = children.iter().map(|v| v.to_scalar()).collect::<Vec<_>>();
        let poly = params.poly(data)?;
        let commitment = params.commitment(&poly);
        Ok(Node {
            commitment,
            poly,
            children: Some(children),
        })
    }

    fn new_leaf(
        params: &Params<C>,
        data: Vec<C::ScalarExt>,
    ) -> Result<Node<C>, Error> {
        let poly = params.poly(data)?;
        let commitment = params.commitment(&poly);
        Ok(Node {
            commitment,
            poly,
            children: None,
        })
    }

    pub fn commitment(&self) -> C {
        self.commitment.to_affine()
    }

    pub fn is_leaf(&self) -> bool {
        self.children.as_ref().map_or(false,|cc| cc.len() > 0)
    }

    pub fn to_scalar(&self) -> C::ScalarExt {
        point_to_scalar(&self.commitment.to_affine())
    }

    
    pub fn describe(&self) -> String {
        return self.describe_internal(0);
    }

    fn describe_internal(&self, lvl: usize) -> String {
        let us = format!("Level {}: {:?}\n",lvl,self);
        let children = self.children.as_ref()
            .map_or(
                vec!["Level {}: Data layer".to_string()],
                |c| c.iter().map(|c| c.describe_internal(lvl+1))
            .collect::<Vec<_>>());
        us + &children.join("\n")
    }
}

fn prover_recurse<'a,C:CurveAffine>(p :&Params<C>, curr_pos:u64, parent: &'a Node<C>, 
    isroot: bool) -> Vec<(ProverQuery<'a,C>, VerifierQuery<C>)> {
    let index_in_layer = curr_pos % p.arity as u64;
    let eval_to = C::ScalarExt::from(index_in_layer);
    let next_pos = (curr_pos - index_in_layer) / p.arity as u64;
    let pq = ProverQuery {
            point: eval_to.clone(),
            poly: &parent.poly,
            blind: Blind(C::ScalarExt::zero()),
    };
    // XXX avoid that double eval for verifier ?
    let eval = eval_polynomial(&parent.poly,eval_to);
    //let eval = parent.poly.iter().rev()
        //.fold(C::ScalarExt::zero(), |acc, coeff| acc * point + coeff)

    let vq :(C,C::ScalarExt) = match isroot {
        false => (parent.commitment.to_affine(),eval),
        // hack to avoid making a special case for the root - the verifier is
        // gonna fill this in.
        true => (C::identity(),eval),
    };

    let mut root = vec![(pq,vq)]; 
    if next_pos < p.arity  as u64{
        return root;
    }
    let children  = parent.children.as_ref().unwrap();
    let children_queries = prover_recurse(p,next_pos, children.get(index_in_layer as usize).unwrap(),false);
    root.extend(children_queries);
    root
}

pub struct Proof<C: CurveAffine>{
    transcript: Vec<u8>,
    // contains the commitment and the evaluation of the polynomial 
    // the evaluation point (x_i) is provided by the verifier
    // in SNARK the evaluation result (y_i) will be given as witness by verifier
    queries: Vec<VerifierQuery<C>>,
}

// (commitment, evaluation result of the polynomial) - the positions are
// given by the verifier
type VerifierQuery<C> = (C,<C as CurveAffine>::ScalarExt);



// verifer_recurse gives all the indexes at which the verifier should queries
// all the polynomials given by the prover.
fn verifier_recurse(arity: usize, curr_pos: u64) -> Vec<u64> {
    let index_in_layer = curr_pos % arity as u64;
    let next_pos = (curr_pos - index_in_layer) / arity as u64;
    let mut root = vec![index_in_layer];
    if next_pos < arity as u64{
        return root;
    }
    let children = verifier_recurse(arity,next_pos);
    root.extend(children);
    root
}


impl<C> Debug for Node<C>
where
    C: CurveAffine,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        f.debug_struct("Node")
            .field("comm",&(format!("{:?}",self.commitment)[16..22]).to_string())
            .field("childrens", &self.children.as_ref()
                .map_or("None".to_string(), |v| format!("{}",v.len()).to_string()))
            .finish()
    }
}

fn point_to_scalar<C: CurveAffine>(point: &C) -> C::ScalarExt {
    let mut transcript = Blake2bWrite::<Vec<u8>, C, Challenge255<C>>::init(vec![]);
    transcript.write_point(point.clone()).unwrap();
    transcript.squeeze_challenge().get_scalar()
}


#[derive(Debug, Error)]
pub enum Error {
    #[error("Not a power of two")]
    NotPowerOfTwo,
    #[error("Invalid size (wrt to params)")]
    InvalidSize,
    #[error("Invalid proof: {0}")]
    InvalidProof(String),
}

#[cfg(test)]
mod test {
    
    use halo2::pasta::{EpAffine, Fq};
    use halo2::arithmetic::FieldExt;
    use super::*;

    #[test]
    fn verkle_tree() {
        let n = 16;
        let arity = 4;
        let params = Params::<EpAffine>::new(n,arity).expect("invalid params");
        let data = (0..n).map(|_| Fq::rand()).collect::<Vec<_>>(); 
        let root = params.build_tree(data).expect("cant build tree");
        let commitment = root.commitment();
        println!("root1: {:?}",root);
        println!("{}",root.describe());
        let pos = vec![5];
        let proof = params.openings(&root,&pos).expect("cant build proof");
        params.verify_proof(proof,&commitment,&pos).expect("valid proofs");

        let mut inv_proof = params.openings(&root,&pos).expect("cant build proof");
        inv_proof.queries[0].1 = Fq::rand();
        params.verify_proof(inv_proof,&commitment,&pos).expect_err("supposed to be invalid");
    }
}
