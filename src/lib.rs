use rand::Rng;
use std::convert::Infallible;
use std::str::FromStr;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Atom(String);

impl Into<String> for Atom {
    fn into(self) -> String {
        self.0
    }
}

impl FromStr for Atom {
    type Err = Infallible; // TODO: numbers
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self(String::from(s)))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Variable {
    name: VariableName,
    alias: String,
    bound_to: Option<VariableBinding>,
}

impl Variable {
    pub fn new_named<Generator: Rng, N: AsRef<str>>(name: N, rng: &mut Generator) -> Self {
        Self {
            name: VariableName::Name(String::from(name.as_ref())),
            alias: Self::gen_alias(rng),
            bound_to: None,
        }
    }
    pub fn new_anonymous<Generator: Rng>(rng: &mut Generator) -> Self {
        Self {
            name: VariableName::Anonymous,
            alias: Self::gen_alias(rng),
            bound_to: None,
        }
    }
    fn gen_alias<Generator: Rng>(rng: &mut Generator) -> String {
        format!("var_{}", rng.gen::<u8>())
    }
    pub fn bind(&mut self, binding: VariableBinding) {
        self.bound_to = Some(binding);
    }
    fn resolve(&self) -> Option<Atom> {
        match self.bound_to {
            Some(VariableBinding::Atom(ref a)) => Some(a.clone()),
            Some(VariableBinding::Variable(ref v)) => v.resolve(),
            None => None,
        }
    }
    fn resolves_to(&self, other: &Atom) -> bool {
        if let Some(ref a) = self.resolve() {
            a == other
        } else {
            false
        }
    }
    fn is_bound(&self) -> bool {
        return self.bound_to.is_some();
    }
    fn corefers_to(&self, other: &Variable) -> bool {
        match (&self.bound_to, &other.bound_to) {
            (
                Some(VariableBinding::Variable(ref my_v)),
                Some(VariableBinding::Variable(ref other_v)),
            ) => my_v == other_v,
            (_, _) => false,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Term {
    Atom(Atom),
    Variable(Variable),
    Functor(Box<Functor>),
}

impl Term {
    pub fn atom_from_str(s: &str) -> Self {
        Self::Atom(Atom::from_str(s).unwrap())
    }
    pub fn variable_from_str<Generator: Rng, N: AsRef<str>>(name: N, rng: &mut Generator) -> Self {
        Self::Variable(Variable::new_named(name, rng))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum VariableBinding {
    Variable(Box<Variable>),
    Atom(Atom),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum VariableName {
    Anonymous,
    Name(String),
}

pub type Arity = usize;

#[derive(Clone, Debug, PartialEq)]
pub enum FunctorState {
    NotYetMatched,
    Matched,
    NoMatch,
    Fulfilled,
}

// Conjunction (,) is a 0-arity functor
#[derive(Clone, Debug)]
pub struct Functor {
    name: Atom,
    args: Vec<Term>,
    body: Vec<Box<Functor>>,
    state: FunctorState,
    ix: usize,
}

impl PartialEq for Functor {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.args.len() == other.args.len()
    }
}

impl Eq for Functor {}

impl Functor {
    pub fn new_fact(name: Atom, args: Vec<Term>) -> Self {
        Self::new_rule(name, args, Vec::new())
    }
    pub fn new_rule(name: Atom, args: Vec<Term>, body: Vec<Box<Functor>>) -> Self {
        Self {
            name,
            args,
            body,
            state: FunctorState::NotYetMatched,
            ix: 0,
        }
    }
    fn is_not_yet_matched(&self) -> bool {
        self.state == FunctorState::NotYetMatched
    }
}

#[derive(Clone, Debug)]
pub struct Database {
    facts: Vec<Functor>,
}

impl Default for Database {
    fn default() -> Self {
        Self::new()
    }
}

impl Database {
    pub fn new() -> Self {
        Self {
            facts: Vec::default(),
        }
    }
    pub fn add(&mut self, mut functor: Functor) {
        functor.ix = self.facts.len();
        self.facts.push(functor);
    }
    pub fn from_rules(rules: Vec<Functor>) -> Self {
        let mut db = Self::new();
        for (ix, mut functor) in rules.into_iter().enumerate() {
            functor.ix = ix;
            db.facts.push(functor);
        }
        db
    }
    pub fn satisfy<'a>(&mut self, goal: Functor) -> Option<Functor> {
        let mut db = self.clone();
        let g = goal.clone();
        let mut matches = db.facts.iter_mut();
        while let Some(mut matched) = matches.next() {
            if matched == &g {
                let g = goal.clone();
                let unified = self.unify(&mut matched, g);
                println!("unified {:?}", unified);
                if unified.is_some() {
                    return unified;
                }
            }
        }
        None
    }
    fn unify(&self, fst: &mut Functor, mut snd: Functor) -> Option<Functor> {
        use std::borrow::BorrowMut;
        for (fst_term, snd_term) in fst.args.iter_mut().zip(snd.args.iter_mut()) {
            println!("fst_term {:?}", fst_term);
            println!("snd_term {:?}", snd_term);
            match (fst_term, snd_term) {
                (Term::Atom(fst_atom), Term::Atom(snd_atom)) if fst_atom == snd_atom => continue,
                (Term::Atom(_), Term::Atom(_)) => return None,
                (Term::Atom(fst_atom), Term::Variable(v)) if v.resolves_to(fst_atom) => continue,
                (Term::Atom(_), Term::Variable(v)) if v.is_bound() => return None,
                (Term::Atom(a), Term::Variable(v)) => v.bind(VariableBinding::Atom(a.clone())),
                (Term::Atom(_), Term::Functor(_)) => return None,
                (Term::Variable(v), Term::Atom(snd_atom)) if !v.is_bound() => {
                    v.bind(VariableBinding::Atom(snd_atom.clone()))
                }
                (Term::Variable(v), Term::Atom(snd_atom)) if v.resolves_to(snd_atom) => continue,
                (Term::Variable(_), Term::Atom(_)) => return None,
                (Term::Variable(fst_v), Term::Variable(snd_v)) => {
                    match (fst_v.resolve(), snd_v.resolve()) {
                        (None, None) => {
                            fst_v.bind(VariableBinding::Variable(Box::new(snd_v.clone())));
                            snd_v.bind(VariableBinding::Variable(Box::new(fst_v.clone())));
                        }
                        (Some(Atom(a)), None) => snd_v.bind(VariableBinding::Atom(Atom(a))),
                        (None, Some(Atom(a))) => fst_v.bind(VariableBinding::Atom(Atom(a))),
                        (Some(Atom(_)), Some(Atom(_))) => return None,
                    }
                }
                (Term::Variable(_), Term::Functor(_)) => return None,
                (Term::Functor(_), Term::Atom(_)) => return None,
                (Term::Functor(_), Term::Variable(_)) => return None,
                (Term::Functor(fst_f), Term::Functor(snd_f)) => {
                    if self.unify(fst_f.borrow_mut(), *snd_f.clone()).is_some() {
                        continue;
                    } else {
                        return None;
                    }
                }
            };
        }
        Some(snd)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::thread_rng;
    #[test]
    fn satisfy_unary() {
        let mut gen = thread_rng();
        let mut db = Database::from_rules(vec![Functor::new_fact(
            Atom(String::from("cool")),
            vec![Term::atom_from_str("rust")],
        )]);
        let goal = Functor::new_fact(
            Atom(String::from("cool")),
            vec![Term::variable_from_str("X", &mut gen)],
        );
        let answer = db.satisfy(goal).expect("answer");
        if let Some(Term::Variable(v)) = answer.args.get(0) {
            assert_eq!(
                v.resolve().expect("satisfy_unary v resolved"),
                Atom::from_str("rust").unwrap()
            );
        } else {
            panic!("satisfy_unary variable unbound")
        }
    }
    #[test]
    fn satisfy_two() {
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
                Term::atom_from_str("chocolate"),
            ],
        );
        let answer = db.satisfy(goal).expect("answer");
        if let Some(Term::Variable(v)) = answer.args.get(0) {
            assert_eq!(
                v.resolve().expect("satisfy_two v resolved"),
                Atom::from_str("sam").unwrap()
            )
        } else {
            panic!("satisfy_two variable unbound")
        }
    }
    #[test]
    fn satisfy_backtrack() {
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
        if let Some(Term::Variable(v)) = answer.args.get(0) {
            assert_eq!(
                v.resolve().expect("satisfy_backtrack v resolved"),
                Atom::from_str("popeye").unwrap()
            )
        } else {
            panic!("satisfy_backtrack variable unbound")
        }
    }
    #[test]
    fn satisfy_fail() {
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
                Term::atom_from_str("oranges"),
            ],
        );
        assert!(db.satisfy(goal).is_none())
    }
    #[test]
    fn satisfy_structure() {
        let mut gen = thread_rng();
        let r1 = Functor::new_fact(
            Atom::from_str("person").unwrap(),
            vec![
                Term::atom_from_str("sam"),
                Term::Functor(Box::new(Functor::new_fact(
                    Atom::from_str("name").unwrap(),
                    vec![Term::atom_from_str("sam")],
                ))),
            ],
        );
        let mut db = Database::from_rules(vec![r1]);
        let goal = Functor::new_fact(
            Atom::from_str("person").unwrap(),
            vec![
                Term::variable_from_str("X", &mut gen),
                Term::Functor(Box::new(Functor::new_fact(
                    Atom::from_str("name").unwrap(),
                    vec![Term::atom_from_str("sam")],
                ))),
            ],
        );
        let answer = db.satisfy(goal).expect("satisfy_structure answer");
        if let Some(Term::Variable(v)) = answer.args.get(0) {
            assert_eq!(
                v.resolve().expect("satisfy_structure v resolved"),
                Atom::from_str("sam").unwrap()
            )
        } else {
            panic!("satisfy_structure variable unbound")
        }
    }
}
