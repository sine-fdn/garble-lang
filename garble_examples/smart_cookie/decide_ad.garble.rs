fn main(user_state: (u128, (u8, [UserInterest; 16])), website_key: u128) -> AdDecisionResult {
    if is_signature_ok(user_state) {
        let sums = [0u8; 6]; // for the 6 user interests
        match user_state {
            (signature, (_, interests)) => {
                let sums =
                    interests.fold(sums, |sums: [u8; 6], interest: UserInterest| -> [u8; 6] {
                        match interest {
                            UserInterest::None => sums,
                            UserInterest::Luxury => sums.update(1, sums[1] + 1),
                            UserInterest::Cars => sums.update(2, sums[2] + 1),
                            UserInterest::Politics => sums.update(3, sums[3] + 1),
                            UserInterest::Sports => sums.update(4, sums[4] + 1),
                            UserInterest::Arts => sums.update(5, sums[5] + 1),
                        }
                    });
                let max_interest = 0..6.fold(
                    (0usize, 0u8),
                    |max_interest: (usize, u8), i: usize| -> (usize, u8) {
                        if sums[i] > max_interest.1 {
                            (i, sums[i])
                        } else {
                            max_interest
                        }
                    }
                );
                AdDecisionResult::Ok(match max_interest.0 {
                    0 => UserInterest::None,
                    1 => UserInterest::Luxury,
                    2 => UserInterest::Cars,
                    3 => UserInterest::Politics,
                    4 => UserInterest::Sports,
                    5 => UserInterest::Arts,
                    _ => UserInterest::None,
                })
            }
        }
    } else {
        AdDecisionResult::InvalidSignature
    }
}

fn is_signature_ok(user_state: (u128, (u8, [UserInterest; 16]))) -> bool {
    // todo:
    true
}

enum AdDecisionResult {
    InvalidSignature,
    Ok(UserInterest),
}

enum UserInterest {
    None,
    Luxury,
    Cars,
    Politics,
    Sports,
    Arts,
}
