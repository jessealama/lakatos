import ts from "typescript";

/** The identifiers an atom references by name: every identifier that is
 * not a property name, the right of a qualified name, or an object key.
 * Binders and globals are among them; callers decide what each is. */
export function freeIdentifiers(expr: string): Set<string> {
  const sf = ts.createSourceFile(
    "__expr.ts",
    `(${expr});`,
    ts.ScriptTarget.Latest,
    true,
  );
  const found = new Set<string>();
  const visit = (node: ts.Node): void => {
    if (ts.isIdentifier(node)) {
      const p = node.parent;
      const isPropName = ts.isPropertyAccessExpression(p) && p.name === node;
      const isQualified = ts.isQualifiedName(p) && p.right === node;
      const isObjKey = ts.isPropertyAssignment(p) && p.name === node;
      if (!isPropName && !isQualified && !isObjKey) found.add(node.text);
    }
    ts.forEachChild(node, visit);
  };
  visit(sf);
  return found;
}
