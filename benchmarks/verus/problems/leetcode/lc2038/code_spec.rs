use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
	pub open spec fn alice_moves_prefix(colors: Seq<char>, end: int) -> int
		recommends
			0 <= end <= colors.len(),
			forall |i: int| 0 <= i < colors.len() ==> colors[i] == 'A' || colors[i] == 'B',
		decreases end,
	{
		if end < 3 {
			0
		} else {
			Self::alice_moves_prefix(colors, end - 1)
				+ if colors[end - 3] == 'A' && colors[end - 2] == 'A' && colors[end - 1] == 'A' {
					1int
				} else {
					0int
				}
		}
	}

	pub open spec fn bob_moves_prefix(colors: Seq<char>, end: int) -> int
		recommends
			0 <= end <= colors.len(),
			forall |i: int| 0 <= i < colors.len() ==> colors[i] == 'A' || colors[i] == 'B',
		decreases end,
	{
		if end < 3 {
			0
		} else {
			Self::bob_moves_prefix(colors, end - 1)
				+ if colors[end - 3] == 'B' && colors[end - 2] == 'B' && colors[end - 1] == 'B' {
					1int
				} else {
					0int
				}
		}
	}

	pub fn winner_of_game(colors: String) -> (result: bool)
		requires
			1 <= colors@.len() <= 100_000,
			forall |i: int| 0 <= i < colors@.len() ==> colors@[i] == 'A' || colors@[i] == 'B',
		ensures
			result <==> Self::alice_moves_prefix(colors@, colors@.len() as int)
				> Self::bob_moves_prefix(colors@, colors@.len() as int),
	{
		let len = colors.as_str().unicode_len();
		if len < 3 {
			return false;
		}

		let mut i: usize = 1;
		let mut alice: i32 = 0;
		let mut bob: i32 = 0;

		while i + 1 < len {
			let left = colors.as_str().get_char(i - 1);
			let mid = colors.as_str().get_char(i);
			let right = colors.as_str().get_char(i + 1);
			if left == 'A' && mid == 'A' && right == 'A' {
				alice = alice + 1;
			}
			if left == 'B' && mid == 'B' && right == 'B' {
				bob = bob + 1;
			}
			i = i + 1;
		}

		alice > bob
	}
}

}
