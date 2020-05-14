use table_maker::statement::Statement;

fn table_mode() {
    let input = {
        let mut buf = String::new();
        std::io::stdin().read_line(&mut buf).unwrap();
        buf = buf.trim().to_string();
        buf
    };

    let parsed = input.parse::<Statement>().unwrap_or_else(|err| {
        println!("Parsing failed with error: {}", err);
        std::process::exit(1);
    });

    println!("Result:\n{:?}", parsed);
    parsed.generate_table(&input);
}

fn prove_mode() {
    let mut input = String::new();

    loop {
        let mut temp = String::new();
        std::io::stdin().read_line(&mut temp).unwrap();
        if temp.trim().is_empty() {
            break;
        }
        input.push('\n');
        input.push_str(temp.trim());
    }

    let (mut p, c) = table_maker::argument::parse_writeup(&input).unwrap();

    println!("Solving...");

    let result = table_maker::argument::prove_validity(&mut p, &c);

    match result {
        Some(true) => println!("Argument is valid"),
        Some(false) => println!("Argument implies the complement of the conclusion"),
        None => println!("Could not determine whether the argument is valid"),
    }
}

fn main() {
    if Some("--table") == std::env::args().nth(1).as_deref() {
        table_mode();
    } else {
        prove_mode();
    }
}

/*use std::str::FromStr;

const TPTP_PATH: &str = "/home/salix/Documents/TPTP-v7.3.0";

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Language {
    Thf,
    Tff,
    Fof,
    Cnf,
}

impl FromStr for Language {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "thf" => Ok(Language::Thf),
            "tff" => Ok(Language::Tff),
            "fof" => Ok(Language::Fof),
            "cnf" => Ok(Language::Cnf),
            _ => Err(format!("Invalid Language '{}'", s)),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Role {
    Axiom,
    Hypothesis,
    Definition,
    Assumption,
    Lemma,
    Theorem,
    Corollary,
    Conjecture,
    NegatedConjecture,
    Plain,
    Type,
    Unknown,
}

impl FromStr for Role {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "axiom" => Ok(Role::Axiom),
            "hypothesis" => Ok(Role::Hypothesis),
            "definition" => Ok(Role::Definition),
            "assumption" => Ok(Role::Assumption),
            "lemma" => Ok(Role::Lemma),
            "theorem" => Ok(Role::Theorem),
            "corollary" => Ok(Role::Corollary),
            "conjecture" => Ok(Role::Conjecture),
            "negated_conjecture" => Ok(Role::NegatedConjecture),
            "plain" => Ok(Role::Plain),
            "type" => Ok(Role::Type),
            "unknown" => Ok(Role::Unknown),
            _ => Err(format!("Invalid Role '{}'", s)),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Formula {
    language: Language,
    name: String,
    role: Role,
    formula: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Problem {
    includes: Vec<String>,
    formulas: Vec<Formula>,
}

fn facts(s: &str) -> Vec<(String, Vec<String>)> {
    let s = s.lines().filter(|l| !l.starts_with('%') && !l.is_empty()).collect::<String>();

    s
        .split(").")
        .map(|f| f.trim())
        .filter(|f| !f.is_empty())
        .map(|f| {
            let open_paren = f.find('(').unwrap();
            let close_paren = /*f.rfind(')').unwrap()*/f.len();
            let name = f[..open_paren].to_string();
            let args = f[open_paren + 1..close_paren].to_string();

            let args = args.split(',').map(|a| a.trim().to_string()).collect();
            (name, args)
        })
        .collect()
}

impl FromStr for Problem {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut facts = facts(s);

        let includes = facts.drain_filter(|(name, _)| name == "include").map(|(_, arg)| arg[0][1..arg[0].len() - 1].to_string()).collect();
        let formulas = facts.into_iter().map(|(lang, mut args)| {
            Ok(Formula {
                language: lang.parse::<Language>()?,
                name: mem::take(&mut args[0]),
                role: args[1].parse::<Role>()?,
                formula: mem::take(&mut args[2]),
            })
        }).collect::<Result<_, String>>()?;

        Ok(Problem {
            includes,
            formulas,
        })
    }
}

fn tptp_mode() {
    let problem = std::fs::read_to_string(Path::new(TPTP_PATH).join("Problems/BOO/BOO001-1.p")).unwrap();
    let problem = problem.parse::<Problem>().unwrap();

    println!("{:?}", problem);
}*/