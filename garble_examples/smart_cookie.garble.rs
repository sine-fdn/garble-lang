pub fn init(user_state: (), website_key: u128) -> (u128, (u8, [UserInterest; 16])) {
    let logged_interest_counter = 0u8;
    let user_state = (logged_interest_counter, [UserInterest::None; 16]);
    let signed = sign(user_state, website_key);
    (signed, user_state)
}

pub fn log_interest(
    user_state: (u128, (u8, [UserInterest; 16])),
    website_interest_and_key: (UserInterest, u128),
) -> LogInterestResult {
    let user_interest = website_interest_and_key.0;
    let signing_key = website_interest_and_key.1;
    if is_signature_ok(user_state) {
        let counter = user_state.1 .0;
        let interests = user_state.1 .1;
        let next_state = (
            (counter + 1) % 16,
            interests.update(counter as usize, user_interest),
        );
        let next_signature = sign(next_state, signing_key);
        LogInterestResult::Ok(next_signature, next_state)
    } else {
        LogInterestResult::InvalidSignature
    }
}

pub fn decide_ad(user_state: (u128, (u8, [UserInterest; 16])), website_key: u128) -> AdDecisionResult {
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

fn sign(user_state: (u8, [UserInterest; 16]), website_signing_key: u128) -> u128 {
    // todo:
    0
}

enum LogInterestResult {
    InvalidSignature,
    Ok(u128, (u8, [UserInterest; 16])),
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
