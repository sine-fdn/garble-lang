fn main(
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

enum UserInterest {
    None,
    Luxury,
    Cars,
    Politics,
    Sports,
    Arts,
}
