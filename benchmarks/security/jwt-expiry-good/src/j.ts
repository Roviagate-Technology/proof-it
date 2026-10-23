import jwt from "jsonwebtoken";
export function check(token: string, key: string) { return jwt.verify(token, key, { algorithms: ["RS256"] }); }
