use amateurlog::*;
use rand::thread_rng;
use std::str::FromStr;
fn main() {
    let mut gen = thread_rng();
    let r1 = Functor::new_fact(
        Atom::from_str("likes").unwrap(),
        vec![Term::atom_from_str("sam"), Term::atom_from_str("chocolate")],
    );
    let r2 = Functor::new_fact(
        Atom::from_str("likes").unwrap(),
        vec![Term::atom_from_str("popeye"), Term::atom_from_str("treats")],
    );
    let mut db = Database::from_rules(vec![r1, r2]);
    let goal = Functor::new_fact(
        Atom::from_str("likes").unwrap(),
        vec![
            Term::variable_from_str("X", &mut gen),
            Term::atom_from_str("treats"),
        ],
    );
    let answer = db.satisfy(goal).expect("answer");
    println!("answer: {:?}", answer);
}
