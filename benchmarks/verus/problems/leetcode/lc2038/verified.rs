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

	proof fn lemma_alice_step(colors: Seq<char>, end: int)
		requires
			3 <= end <= colors.len(),
			forall |i: int| 0 <= i < colors.len() ==> colors[i] == 'A' || colors[i] == 'B',
		ensures
			Self::alice_moves_prefix(colors, end)
				== Self::alice_moves_prefix(colors, end - 1)
					+ if colors[end - 3] == 'A' && colors[end - 2] == 'A' && colors[end - 1] == 'A' {
						1int
					} else {
						0int
					},
	{
	}

	proof fn lemma_bob_step(colors: Seq<char>, end: int)
		requires
			3 <= end <= colors.len(),
			forall |i: int| 0 <= i < colors.len() ==> colors[i] == 'A' || colors[i] == 'B',
		ensures
			Self::bob_moves_prefix(colors, end)
				== Self::bob_moves_prefix(colors, end - 1)
					+ if colors[end - 3] == 'B' && colors[end - 2] == 'B' && colors[end - 1] == 'B' {
						1int
					} else {
						0int
					},
	{
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
			proof {
				assert(Self::alice_moves_prefix(colors@, len as int) == 0);
				assert(Self::bob_moves_prefix(colors@, len as int) == 0);
			}
			return false;
		}

		let mut i: usize = 1;
		let mut alice: i32 = 0;
		let mut bob: i32 = 0;

		while i + 1 < len
			invariant
				3 <= len <= 100_000,
				len == colors@.len(),
				forall |k: int| 0 <= k < colors@.len() ==> colors@[k] == 'A' || colors@[k] == 'B',
				1 <= i < len,
				alice as int == Self::alice_moves_prefix(colors@, i as int + 1),
				bob as int == Self::bob_moves_prefix(colors@, i as int + 1),
				0 <= alice as int <= i as int,
				0 <= bob as int <= i as int,
			decreases len - i,
		{
			let ghost old_i: int = i as int;
			let left = colors.as_str().get_char(i - 1);
			let mid = colors.as_str().get_char(i);
			let right = colors.as_str().get_char(i + 1);

			proof {
				assert(3 <= old_i + 2 <= colors@.len());
				Self::lemma_alice_step(colors@, old_i + 2);
				Self::lemma_bob_step(colors@, old_i + 2);
			}

			if left == 'A' && mid == 'A' && right == 'A' {
				alice = alice + 1;
			}
			if left == 'B' && mid == 'B' && right == 'B' {
				bob = bob + 1;
			}

			proof {
				assert(colors@[old_i - 1] == left);
				assert(colors@[old_i] == mid);
				assert(colors@[old_i + 1] == right);

				assert(alice as int
					== Self::alice_moves_prefix(colors@, old_i + 1)
						+ if left == 'A' && mid == 'A' && right == 'A' { 1int } else { 0int });
				assert(bob as int
					== Self::bob_moves_prefix(colors@, old_i + 1)
						+ if left == 'B' && mid == 'B' && right == 'B' { 1int } else { 0int });

				assert(alice as int == Self::alice_moves_prefix(colors@, old_i + 2));
				assert(bob as int == Self::bob_moves_prefix(colors@, old_i + 2));
			}

			i = i + 1;
		}

		proof {
			assert(i + 1 == len);
			assert(alice as int == Self::alice_moves_prefix(colors@, len as int));
			assert(bob as int == Self::bob_moves_prefix(colors@, len as int));
		}

		alice > bob
	}
}

}
