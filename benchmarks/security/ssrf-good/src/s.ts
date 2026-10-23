export async function proxy(req: any) { return fetch("https://api.example.com/items/" + encodeURIComponent(req.query.id)); }
