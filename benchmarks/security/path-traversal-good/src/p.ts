import fs from "fs";
import path from "path";
export function read(req: any, res: any) { fs.readFile("/srv/files/" + path.basename(req.params.name), (e, d) => res.send(d)); }
