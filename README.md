# Archetype Entity Component System

AECS is an entity component system which manages entities by sorting them into separate buckets based on the components they have. Buckets in memory make use of the [structure of arrays](https://wikiless.org/wiki/AOS_and_SOA?lang=en) (SoA) layout which is computed at runtime based on the currently available archetypes.

NOTE: this is currently in progress thus nothing really works yet

## Usage

```zig
const Data = struct {
    position: Vec2,
    velocity: Vec2,
    health: u32,
};

const Model = aecs.Model(Data);
```
