import { execFile } from "child_process";
export function thumb(req: any) { execFile("convert", [req.body.path, "out.png"]); }
