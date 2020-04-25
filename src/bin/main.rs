use table_maker::argument;
use table_maker::statement::Statement;
use table_maker::Variable;

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

fn main() {
    if Some("--table") == std::env::args().nth(1).as_deref() {
        table_mode();
    } else {
        // forall(x): (A(x) -> B(x))
        // exists(x): (A(x))
        // -----------------
        // exists(x): (B(x))

        // weaken, then modus ponens

        // Prove:
        // A - B subset A

        // (a ^ !b) -> c
        // c -> a

        // C = A - B
        // { x | x elem A ^ not (x elem B) }

        let mut all_statements = vec!["a -> b", "a ^ b"]
            .into_iter()
            .map(|p| p.parse::<Statement>().unwrap())
            .collect::<Vec<_>>();

        let conclusion = Statement::Variable(Variable("b".to_string()));

        assert_eq!(
            Some(true),
            argument::prove_validity(&mut all_statements, &conclusion)
        );

        /*for m in matches.iter() {
            println!("Match:");
            for m_inner in m.iter() {
                println!("\t{} => {}", m_inner.0, m_inner.1);

                let temp = format!("\t\t{}", m_inner.0.try_match(m_inner.1).unwrap()).replace("\n", "\n\t\t");
                println!("{}", temp);
            }
            println!();
        }*/
    }
}
