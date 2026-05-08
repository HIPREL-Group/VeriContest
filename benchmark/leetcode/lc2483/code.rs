impl Solution {
	pub fn best_closing_time(customers: String) -> i32 {
		let len = customers.as_str().unicode_len();
		let mut i: usize = 0;
		let mut score: i32 = 0;
		let mut best_score: i32 = 0;
		let mut best_hour: usize = 0;

		while i < len {
			let c = customers.as_str().get_char(i);
			if c == 'Y' {
				score = score + 1;
			} else {
				score = score - 1;
			}
			if best_score < score {
				best_score = score;
				best_hour = i + 1;
			}
			i = i + 1;
		}

		best_hour as i32
	}
}
