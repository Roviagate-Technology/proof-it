// Read from the environment at runtime; no key material in source.
export const stripe = process.env.STRIPE_SECRET_KEY;
