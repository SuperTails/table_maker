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
    std::io::stdin().read_line(&mut input).unwrap();
    println!("Result: {:?}", table_maker::prove(&input).unwrap());
}

fn main() {
    if Some("--table") == std::env::args().nth(1).as_deref() {
        table_mode();
    } else {
        prove_mode();
    }
}
