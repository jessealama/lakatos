// An exported const bound to an arrow function. Qualified name: `twice`.
/** @ensures{twiceDoubles} forall (x: int) { twice(x) === x + x } */
export const twice = (x: number): number => x + x;
