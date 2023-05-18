use crate::backend::{
    commitment::*,
    costs::{logmn, JBatching, JCommit},
    proof_execution::*,
};
use crate::nfa::{EPSILON, NFA};

#[cfg(feature = "metrics")]
use crate::metrics::{log, log::Component};

// gen R1CS object, commitment, make step circuit for nova
pub fn run_backend(
    nfa: NFA,
    doc: Vec<String>,
    batching_type: Option<JBatching>,
    commit_doctype: Option<JCommit>,
    temp_batch_size: usize, // this may be 0 if not overridden, only use to feed into R1CS object
) {
    // make udoc (TODO not twice)
    let mut batch_doc = doc.clone();

    batch_doc.push(EPSILON.clone()); // only required for nlookup, so need some additoinal work
                                     // somewhere :(

    let mut usize_doc = vec![];
    for c in batch_doc.clone().into_iter() {
        let u = nfa.ab_to_num(&c.to_string());
        usize_doc.push(u);
    }

    #[cfg(feature = "metrics")]
    log::tic(Component::Compiler, "Commitment", "Commitment Generations");
    let reef_commit = ReefCommitment::gen_commitment(usize_doc); // todo clone

    #[cfg(feature = "metrics")]
    log::stop(Component::Compiler, "Commitment", "Commitment Generations");

    #[cfg(feature = "metrics")]
    log::tic(Component::Compiler, "Commitment", "Commitment Proof");

    // optional? - TODO threading?
    run_consistency_proof(doc.clone(), reef_commit.clone());

    #[cfg(feature = "metrics")]
    log::stop(Component::Compiler, "Commitment", "Commitment Proof");

    // main affair
    run_proof(
        nfa,
        doc,
        batching_type,
        commit_doctype,
        temp_batch_size,
        reef_commit,
    );
}

#[cfg(test)]
mod tests {

    use crate::backend::framework::*;
    use crate::backend::r1cs_helper::init;
    use crate::nfa::NFA;
    use crate::regex::Regex;

    fn backend_test(
        ab: String,
        rstr: String,
        doc: Vec<String>,
        batching_type: Option<JBatching>,
        commit_docype: Option<JCommit>,
        batch_size: usize,
    ) {
        let r = Regex::new(&rstr);
        let nfa = NFA::new(&ab[..], r);

        init();
        run_backend(
            nfa.clone(),
            doc.clone(),
            batching_type.clone(),
            commit_docype.clone(),
            batch_size,
        );
    }

    #[test]
    fn e2e_q_overflow() {
        backend_test(
            "abcdefg".to_string(),
            "gaa*bb*cc*dd*ee*f".to_string(),
            ("gaaaaaabbbbbbccccccddddddeeeeeef".to_string())
                .chars()
                .map(|c| c.to_string())
                .collect(),
            Some(JBatching::Nlookup),
            Some(JCommit::Nlookup),
            33,
        );
    }

    #[test]
    fn e2e_substring() {
        backend_test(
            "ab".to_string(),
            "bbb".to_string(),
            ("aaabbbaaa".to_string())
                .chars()
                .map(|c| c.to_string())
                .collect(),
            Some(JBatching::Nlookup),
            Some(JCommit::Nlookup),
            2,
        );

        backend_test(
            "ab".to_string(),
            "bbbaaa".to_string(),
            ("aaabbbaaa".to_string())
                .chars()
                .map(|c| c.to_string())
                .collect(),
            Some(JBatching::NaivePolys),
            Some(JCommit::HashChain),
            2,
        );
    }

    #[test]
    fn e2e_poly_hash() {
        backend_test(
            "ab".to_string(),
            "^a*b*$".to_string(),
            ("aaab".to_string())
                .chars()
                .map(|c| c.to_string())
                .collect(),
            Some(JBatching::NaivePolys),
            Some(JCommit::HashChain),
            0,
        );
        /*        backend_test(
                  "ab".to_string(),
                  "^ab*$".to_string(),
                  &("abbbbbbb".to_string())
                      .chars()
                      .map(|c| c.to_string())
                      .collect(),
                  Some(JBatching::NaivePolys),
                  Some(JCommit::HashChain),
                  vec![0, 2],
              );
              backend_test(
                  "ab".to_string(),
                  "^a*$".to_string(),
                  &("aaaaaaaaaaaaaaaa".to_string())
                      .chars()
                      .map(|c| c.to_string())
                      .collect(),
                  Some(JBatching::NaivePolys),
                  Some(JCommit::HashChain),
                  vec![0, 2, 5],
              );
        */
    }

    #[test]
    fn e2e_poly_nl() {
        backend_test(
            "ab".to_string(),
            "^a*b*$".to_string(),
            ("aaab".to_string())
                .chars()
                .map(|c| c.to_string())
                .collect(),
            Some(JBatching::NaivePolys),
            Some(JCommit::Nlookup),
            0,
        );
        /*    backend_test(
                "ab".to_string(),
                "^a*b*$".to_string(),
                &("aa".to_string()).chars().map(|c| c.to_string()).collect(),
                Some(JBatching::NaivePolys),
                Some(JCommit::Nlookup),
                vec![0, 1, 2],
            );
            backend_test(
                "ab".to_string(),
                "^a*b*$".to_string(),
                &("aaab".to_string())
                    .chars()
                    .map(|c| c.to_string())
                    .collect(),
                Some(JBatching::NaivePolys),
                Some(JCommit::Nlookup),
                vec![0, 2],
            );
            backend_test(
                "ab".to_string(),
                "^ab*$".to_string(),
                &("abbbbbbb".to_string())
                    .chars()
                    .map(|c| c.to_string())
                    .collect(),
                Some(JBatching::NaivePolys),
                Some(JCommit::Nlookup),
                vec![0, 2, 5],
            );
            backend_test(
                "ab".to_string(),
                "^a*$".to_string(),
                &("aaaaaaaaaaaaaaaa".to_string())
                    .chars()
                    .map(|c| c.to_string())
                    .collect(),
                Some(JBatching::NaivePolys),
                Some(JCommit::Nlookup),
                vec![0, 2, 5],
            );
        */
    }

    #[test]
    fn e2e_nl_hash() {
        backend_test(
            "ab".to_string(),
            "^a*b*$".to_string(),
            ("aaab".to_string())
                .chars()
                .map(|c| c.to_string())
                .collect(),
            Some(JBatching::Nlookup),
            Some(JCommit::HashChain),
            0,
        );
        /*  backend_test(
                "ab".to_string(),
                "^a*b*$".to_string(),
                &("aa".to_string()).chars().map(|c| c.to_string()).collect(),
                Some(JBatching::Nlookup),
                Some(JCommit::HashChain),
                vec![0, 1, 2],
            );
            backend_test(
                "ab".to_string(),
                "^a*b*$".to_string(),
                &("aaab".to_string())
                    .chars()
                    .map(|c| c.to_string())
                    .collect(),
                Some(JBatching::Nlookup),
                Some(JCommit::HashChain),
                vec![0, 2],
            );
            backend_test(
                "ab".to_string(),
                "^ab*$".to_string(),
                &("abbbbbbb".to_string())
                    .chars()
                    .map(|c| c.to_string())
                    .collect(),
                Some(JBatching::Nlookup),
                Some(JCommit::HashChain),
                vec![0, 2],
            );
            backend_test(
                "ab".to_string(),
                "^a*$".to_string(),
                &("aaaaaaaaaaaaaaaa".to_string())
                    .chars()
                    .map(|c| c.to_string())
                    .collect(),
                Some(JBatching::Nlookup),
                Some(JCommit::HashChain),
                vec![0, 2, 5],
                // [1,2,3,4,5,6,7,8,
            );
        */
    }

    #[test]
    fn e2e_nl_nl() {
        backend_test(
            "ab".to_string(),
            "^a*b*$".to_string(),
            ("aaab".to_string())
                .chars()
                .map(|c| c.to_string())
                .collect(),
            Some(JBatching::Nlookup),
            Some(JCommit::Nlookup),
            0,
        );
        /*  backend_test(
                "ab".to_string(),
                "^a*b*$".to_string(),
                &("aa".to_string()).chars().map(|c| c.to_string()).collect(),
                Some(JBatching::Nlookup),
                Some(JCommit::Nlookup),
                vec![0, 1, 2],
            );
            backend_test(
                "ab".to_string(),
                "^a*b*$".to_string(),
                &("aaab".to_string())
                    .chars()
                    .map(|c| c.to_string())
                    .collect(),
                Some(JBatching::Nlookup),
                Some(JCommit::Nlookup),
                vec![0, 2],
            );
            backend_test(
                "ab".to_string(),
                "^ab*$".to_string(),
                &("abbbbbbb".to_string())
                    .chars()
                    .map(|c| c.to_string())
                    .collect(),
                Some(JBatching::Nlookup),
                Some(JCommit::Nlookup),
                vec![0, 2, 5],
            );
            backend_test(
                "ab".to_string(),
                "^a*$".to_string(),
                &("aaaaaaaaaaaaaaaa".to_string())
                    .chars()
                    .map(|c| c.to_string())
                    .collect(),
                Some(JBatching::Nlookup),
                Some(JCommit::Nlookup),
                vec![0, 2, 5],
                // [1,2,3,4,5,6,7,8,
            );
        */
    }
}
