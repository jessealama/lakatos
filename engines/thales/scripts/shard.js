// Round-robin rather than contiguous blocks: the manifest is ordered by
// slice, and contiguous blocks would put every class fixture in one shard.
export function shardOf(items, spec) {
  if (spec === undefined || spec === "") return items;
  const m = /^(\d+)\/(\d+)$/.exec(spec);
  if (m === null) {
    throw new Error(`shard spec must look like "2/3", got: ${spec}`);
  }
  const index = Number(m[1]);
  const count = Number(m[2]);
  if (count < 1) throw new Error(`shard count must be at least 1: ${spec}`);
  if (index < 1 || index > count) {
    throw new Error(`shard index out of range for ${count} shards: ${spec}`);
  }
  return items.filter((_, i) => i % count === index - 1);
}
