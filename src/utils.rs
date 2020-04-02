pub fn format_memory(mem: &[u8], line_width: usize) -> String {
    let mut s = String::from("");
    for address in 0..=(mem.len() / line_width) {
        let address = address * line_width;

        s.push_str(&format!("{:04X}: ", address));

        for i in 0..line_width {
            let byte = mem.get(address as usize + i as usize);
            match byte {
                Some(val) => {
                    s.push_str(&format!("{:02X} ", val));
                }
                None => s.push_str("   "),
            }
        }

        s.push_str(" ");

        for i in 0..line_width {
            let byte = mem.get(address as usize + i as usize);
            match byte {
                Some(val) => {
                    if val.is_ascii_alphanumeric() || val.is_ascii_punctuation() || *val == b' ' {
                        s.push_str(&format!("{}", *val as char));
                    } else {
                        s.push_str(".")
                    }
                }
                None => s.push_str(" "),
            }
        }

        s.push_str("\n");
    }

    s
}
