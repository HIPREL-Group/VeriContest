impl Solution {
    pub fn categorize_box(length: i32, width: i32, height: i32, mass: i32) -> String {
        let l: i128 = length as i128;
        let w: i128 = width as i128;
        let h: i128 = height as i128;
        let area: i128 = l * w;
        let volume: i128 = area * h;
        let bulky: bool = length >= 10000 || width >= 10000 || height >= 10000 || volume >= 1_000_000_000;
        let heavy: bool = mass >= 100;
        if bulky && heavy {
            "Both".to_string()
        } else if bulky {
            "Bulky".to_string()
        } else if heavy {
            "Heavy".to_string()
        } else {
            "Neither".to_string()
        }
    }
}
