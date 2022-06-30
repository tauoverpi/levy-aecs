const std = @import("std");
const mem = std.mem;
const meta = std.meta;
const math = std.math;
const assert = std.debug.assert;
const testing = std.testing;

const Type = std.builtin.Type;
const Allocator = std.mem.Allocator;

pub const Entity = enum(u32) { _ };

/// Model: given a data model, construct an entity component storage type
pub fn Model(comptime Spec: type) type {
    return struct {
        entities: EntityMap = .{},
        storage: BucketMap = .{},
        count: u32 = 0,

        pub const EntityMap = std.AutoHashMapUnmanaged(Entity, Pointer);
        pub const BucketMap = std.AutoHashMapUnmanaged(Archetype, Bucket);
        pub const Pointer = struct {
            type: Archetype,
            index: u16,
        };

        /// Archetype: bitset representing the currently active components
        pub const Archetype = enum(Int) {
            empty,
            _,

            /// Backing integer for the bitset
            pub const Int = meta.Int(.unsigned, layout.fields.len);
            pub const Tag = layout.tag;
            pub const void_mask = @intToEnum(Archetype, ~((@as(Int, 1) << layout.split) - 1));

            pub fn add(self: Archetype, tag: Tag) Archetype {
                return @intToEnum(Archetype, @enumToInt(self) | (@as(Int, 1) << @enumToInt(tag)));
            }

            pub fn remove(self: Archetype, tag: Tag) Archetype {
                return @intToEnum(Archetype, @enumToInt(self) & ~(@as(Int, 1) << @enumToInt(tag)));
            }

            pub fn has(self: Archetype, tag: Tag) bool {
                return @enumToInt(self) & (@as(Int, 1) << @enumToInt(tag)) != 0;
            }

            pub fn merge(self: Archetype, other: Archetype) Archetype {
                return @intToEnum(Archetype, @enumToInt(self) | @enumToInt(other));
            }

            pub fn contains(self: Archetype, other: Archetype) bool {
                return @enumToInt(self) & @enumToInt(other) == @enumToInt(other);
            }

            pub fn fromList(tags: []const Tag) Archetype {
                var tmp: Archetype = .empty;

                for (tags) |tag| tmp = tmp.add(tag);

                return tmp;
            }

            pub fn fromType(comptime T: type) Archetype {
                comptime {
                    var tmp: Archetype = .empty;

                    for (meta.fields(T)) |field| {
                        tmp = tmp.add(@field(Tag, field.name));
                    }

                    return tmp;
                }
            }

            pub fn TypeOf(comptime tag: Tag) type {
                return layout.fields[@enumToInt(tag)].field_type;
            }

            pub fn iterator(self: Archetype) Iterator {
                return .{ .type = self };
            }

            pub const Iterator = struct {
                type: Archetype,

                pub fn next(self: *Iterator) ?Tag {
                    const int = @enumToInt(self.type);

                    if (int == 0) return null;

                    const tag = @intToEnum(Tag, @ctz(Int, int));

                    self.type = self.type.remove(tag);

                    return tag;
                }
            };
        };

        pub const Self = @This();

        pub const Name = struct {
            alias: ?@TypeOf(.EnumLiteral) = null,
            component: Archetype.Tag,

            pub fn name(comptime self: Name) []const u8 {
                comptime {
                    if (self.alias) |alias| {
                        return @tagName(alias);
                    } else {
                        return @tagName(self.component);
                    }
                }
            }
        };

        pub fn context(self: *Self, comptime namespace: []const Name) Context(namespace) {
            return .{ .model = self };
        }

        /// Generate a context in which component names are remapped
        pub fn Context(comptime namespace: []const Name) type {
            comptime {
                var norm = blk: {
                    if (namespace.len == 0) {
                        var norm: [layout.fields.len]Name = undefined;

                        for (layout.fields) |field, index| {
                            norm[index] = .{
                                .component = @field(Archetype.Tag, field.name),
                            };
                        }

                        break :blk norm;
                    } else {
                        break :blk namespace[0..namespace.len].*;
                    }
                };

                std.sort.sort(Name, &norm, {}, struct {
                    pub fn lessThan(_: void, comptime lhs: Name, comptime rhs: Name) bool {
                        return @enumToInt(lhs.component) < @enumToInt(rhs.component);
                    }
                }.lessThan);

                return ContextImpl(norm.len, norm);
            }
        }

        // ContextImpl is split into a separate function rather than inlining it
        // such that an equivalent namespace which only differs in the order in
        // which aliases are specified yield the same result.
        fn ContextImpl(comptime namespace_len: usize, comptime namespace: [namespace_len]Name) type {
            return struct {
                model: *Self,

                /// Find the appropriate name within the namespace for the given item
                fn getName(comptime field_name: []const u8) Name {
                    if (namespace.len == 0) {
                        return .{ .tag = @field(Archetype.Tag, field_name) };
                    } else for (namespace) |name| {
                        if (mem.eql(u8, field_name, name.name())) {
                            return name;
                        }
                    } else {
                        const msg = if (namespace.len == 0)
                            "." ++ field_name ++ " is not part of the declared components"
                        else blk: {
                            comptime var msg = "." ++ field_name ++ " is not part of the provided namespace:\n";
                            for (namespace) |name| {
                                msg = msg ++ "\t" ++ @tagName(name.component) ++ "\t\t" ++ @tagName(name.alias) ++ "\n";
                            }
                            break :blk msg;
                        };

                        @compileError(msg);
                    }
                }

                const Metadata = struct {
                    name: Name,
                    mutable: bool,
                };

                fn isMutablePointer(comptime T: type) bool {
                    switch (@typeInfo(T)) {
                        .Pointer => |info| switch (info.size) {
                            .One => if (!info.is_const) {
                                return true;
                            } else @compileError(
                                "`*const T` provided, `T` is preferred as it maps to the same pointer type",
                            ),
                            else => @compileError("query only supports single item pointers (*T)"),
                        },
                        else => return false,
                    }
                }

                fn Child(comptime T: type) type {
                    switch (@typeInfo(T)) {
                        .Pointer => |info| return info.child,
                        else => return T,
                    }
                }

                pub fn query(self: @This(), comptime spec: type) Query(spec) {
                    const mask = comptime blk: {
                        var mask: Archetype = .empty;

                        for (namespace) |name| {
                            if (@hasField(spec, name.name())) {
                                mask = mask.add(name.component);
                            }
                        }

                        break :blk mask;
                    };

                    return .{
                        .it = self.model.storage.iterator(),
                        .type = mask,
                        .map = &self.model.entities,
                    };
                }

                pub fn Query(comptime T: type) type {
                    comptime {
                        const FE = meta.FieldEnum(T);

                        var metadata: [meta.fields(T).len]Metadata = undefined;

                        var index: usize = 0;

                        // Ensure metadata order is consistent with namespace order
                        for (namespace) |name| {
                            if (@hasField(T, name.name())) {
                                const field = meta.fieldInfo(T, @field(FE, name.name()));

                                assert(Child(field.field_type) == Archetype.TypeOf(name.component));

                                metadata[index] = .{
                                    .name = name,
                                    .mutable = isMutablePointer(field.field_type),
                                };

                                index += 1;
                            }
                        }

                        assert(index == metadata.len); // missing fields

                        return QueryImpl(metadata.len, metadata);
                    }
                }

                /// QueryImpl is split into a separate function to reduce the number of instantiations
                /// required as zig uses nominal rather than structural types leading to new types for
                /// each struct given even if it has the exact same set of fields as one specified prior
                /// with the same context. Thus, inspecting just the structure of the given type and
                /// ignoring the uniqueness of it reduces the number of variations of metadata and takes
                /// advantage of lazy evaluation present in zig comptime.
                fn QueryImpl(comptime metadata_len: usize, comptime metadata: [metadata_len]Metadata) type {
                    return struct {
                        type: Archetype,
                        it: BucketMap.Iterator,
                        map: *const EntityMap,

                        pub const Pointers = blk: {
                            var fields: [metadata.len]Type.StructField = undefined;

                            const index = for (metadata) |m, index| {
                                const C = Archetype.TypeOf(m.name.component);
                                if (C == void) break index;
                                fields[index] = .{
                                    .name = m.name.name(),
                                    .field_type = if (m.mutable) [*]C else [*]const C,
                                    .alignment = @alignOf([*]C),
                                    .default_value = null,
                                    .is_comptime = false,
                                };
                            } else metadata.len;

                            break :blk @Type(.{ .Struct = .{
                                .layout = .Auto,
                                .fields = fields[0..index],
                                .decls = &.{},
                                .is_tuple = false,
                            } });
                        };

                        pub const Result = struct {
                            bucket: *Bucket,
                            pointers: Pointers,
                        };

                        fn pointers(bucket: *Bucket) Pointers {
                            var result: Pointers = undefined;

                            var it = bucket.iterator();

                            inline for (metadata) |m| {
                                const FT = Archetype.TypeOf(m.name.component);

                                if (FT != void) {
                                    const ptr = it.findNext(m.name.component) orelse unreachable;

                                    const name = comptime m.name.name(); // stage 1 bug
                                    @field(result, name) = if (m.mutable)
                                        @ptrCast([*]FT, @alignCast(@alignOf(FT), ptr))
                                    else
                                        @ptrCast([*]const FT, @alignCast(@alignOf(FT), ptr));
                                }
                            }

                            return result;
                        }

                        pub fn next(self: *@This()) ?Result {
                            var entry = self.it.next() orelse return null;

                            while (!entry.key_ptr.contains(self.type)) {
                                entry = self.it.next() orelse return null;
                            }

                            entry.value_ptr.commit(self.map);
                            return Result{
                                .bucket = entry.value_ptr,
                                .pointers = pointers(entry.value_ptr),
                            };
                        }
                    };
                }

                pub fn new(self: @This()) Entity {
                    var count = self.model.count;
                    defer self.model.count = count;

                    var limit: u32 = 0xffff_ffff;

                    while (self.model.entities.contains(@intToEnum(Entity, count))) : (limit -= 1) {
                        count += 1;
                    }

                    return @intToEnum(Entity, count);
                }

                pub fn update(
                    self: @This(),
                    gpa: Allocator,
                    entity: Entity,
                    comptime T: type,
                    values: T,
                ) !void {
                    const pointer = blk: {
                        const entry = try self.model.entities.getOrPut(gpa, entity);

                        if (!entry.found_existing) {
                            entry.value_ptr.* = .{
                                .index = undefined,
                                .type = .empty,
                            };
                        }

                        break :blk entry.value_ptr;
                    };

                    const location = pointer.type.merge(Archetype.fromType(T));

                    if (location == .empty) std.debug.todo("handle zero");

                    const bucket = blk: {
                        const entry = try self.model.storage.getOrPut(gpa, location);

                        if (!entry.found_existing) {
                            entry.value_ptr.* = .{
                                .type = location,
                            };
                        }

                        break :blk entry.value_ptr;
                    };

                    if (pointer.type != location) {
                        const index = bucket.len;
                        try bucket.ensureTotalCapacity(gpa, index + 1);
                        bucket.len += 1;

                        if (pointer.type != .empty) {
                            const old = self.model.storage.getPtr(pointer.type) orelse unreachable;
                            old.commit(&self.model.entities);

                            var old_it = old.iterator();
                            var new_it = bucket.iterator();

                            while (old_it.next()) |old_pair| {
                                const ptr = new_it.findNext(old_pair.tag) orelse unreachable;
                                const size = layout.size[@enumToInt(old_pair.tag)];

                                if (size == 0) break; // void tags

                                const old_ptr = old_pair.ptr + size * pointer.index;
                                const new_ptr = ptr + size * index;
                                @memcpy(new_ptr, old_ptr, size);
                            }

                            old.remove(pointer.index);
                        }

                        bucket.entities()[index] = entity;
                        pointer.index = index;
                        pointer.type = location;
                    }

                    var it = bucket.iterator();

                    inline for (namespace) |m| {
                        const name = comptime m.name();
                        if (@hasField(T, name)) {
                            const FT = Archetype.TypeOf(m.component);

                            if (FT != void) {
                                const ptr = it.findNext(m.component) orelse unreachable;
                                const component = @ptrCast([*]FT, @alignCast(@alignOf(FT), ptr));
                                component[pointer.index] = @field(
                                    values,
                                    name,
                                );
                            }
                        }
                    }
                }
            };
        }

        pub const Bucket = struct {
            type: Archetype,
            capacity: u16 = 0,
            bytes: []u8 = &.{},
            free: ?Free = null,
            len: u16 = 0,

            // -- ACCESS --

            pub fn entities(self: Bucket) []Entity {
                const offset = self.bytes.ptr + (self.bytes.len - @sizeOf(Entity) * self.capacity);
                return @ptrCast([*]Entity, @alignCast(@alignOf(Entity), offset))[0..self.len];
            }

            pub fn items(self: Bucket, comptime tag: Archetype.Tag) []Archetype.TypeOf(tag) {
                assert(self.type.has(tag)); // missing component

                const T = Archetype.TypeOf(tag);

                var offset: usize = 0;

                var it = self.type.iterator();
                while (it.next()) |found| {
                    if (found == tag) break;
                    offset += layout.size[@enumToInt(found)];
                }

                offset *= self.capacity;

                const ptr = @alignCast(@alignOf(T), self.bytes.ptr + offset);

                return @ptrCast([*]T, ptr)[0..self.len];
            }

            pub fn iterator(self: *Bucket) Iterator {
                return .{
                    .capacity = self.capacity,
                    .it = self.type.iterator(),
                    .ptr = self.bytes.ptr,
                };
            }

            pub const Iterator = struct {
                capacity: u16,
                it: Archetype.Iterator,
                ptr: [*]u8,

                pub const Pair = struct {
                    tag: Archetype.Tag,
                    ptr: [*]u8,
                };

                pub fn next(self: *Iterator) ?Pair {
                    const tag = self.it.next() orelse return null;

                    defer self.ptr += self.capacity * layout.size[@enumToInt(tag)];

                    return Pair{ .tag = tag, .ptr = self.ptr };
                }

                pub fn findNext(self: *Iterator, tag: Archetype.Tag) ?[*]u8 {
                    while (self.next()) |pair| {
                        if (pair.tag == tag) return pair.ptr;
                    }

                    return null;
                }
            };

            // -- EXPANDING CAPACITY --

            pub fn ensureTotalCapacity(self: *Bucket, gpa: Allocator, new_capacity: u16) !void {
                var better_capacity = self.capacity;
                if (better_capacity >= new_capacity) return;

                while (true) {
                    better_capacity += better_capacity / 2 + 8;
                    if (better_capacity >= new_capacity) break;
                }

                return self.setCapacity(gpa, better_capacity);
            }

            pub fn ensureUnusedCapacity(self: *Bucket, gpa: Allocator, additional_capacity: u16) !void {
                return self.ensureTotalCapacity(gpa, self.len + additional_capacity);
            }

            pub fn setCapacity(self: *Bucket, gpa: Allocator, new_capacity: u16) !void {
                assert(new_capacity >= self.len);

                const alignment = layout.alignment[@ctz(Archetype.Int, @enumToInt(self.type))];

                const size = blk: {
                    var size: usize = 0;
                    var it = self.type.iterator();
                    while (it.next()) |tag| size += layout.size[@enumToInt(tag)];
                    break :blk size;
                };

                const bytes = mem.alignForward(size * new_capacity, @alignOf(Entity)) +
                    @sizeOf(Entity) * new_capacity;

                const new_bytes = try gpa.allocBytes(alignment, bytes, 0, @returnAddress());

                if (self.len == 0) {
                    gpa.free(self.bytes);
                    self.bytes = new_bytes;
                    self.capacity = new_capacity;
                    return;
                }

                var bucket = self.*;
                bucket.bytes = new_bytes;
                bucket.capacity = new_capacity;

                var self_it = self.iterator();
                var new_it = bucket.iterator();

                while (self_it.next()) |self_pair| {
                    const new_pair = new_it.next() orelse unreachable;
                    const len = layout.size[@enumToInt(self_pair.tag)];

                    @memcpy(new_pair.ptr, self_pair.ptr, len * self.len);
                }

                mem.copy(Entity, bucket.entities(), self.entities());

                gpa.free(self.bytes);

                self.* = bucket;
            }

            // -- REMOVING --

            const Free = struct {
                head: u16,
                tail: u16,
            };

            const Node = packed struct {
                next: u16,
                prev: u16,
            };

            /// Mark an entity for removal.
            ///
            /// Removed entities are turned into a doubly-linked list from the first
            /// removed entity to the last which leaves a sparse bucket where the
            /// bucket length no longer matches the actual length of the component
            /// arrays (it's now sparse). To return to a compact representation see
            /// `Model.commit`.
            pub fn remove(self: *Bucket, index: u16) void {
                assert(index < self.len); // out of bounds
                const nodes = @ptrCast([*]Node, self.entities().ptr);

                if (self.free) |*list| {
                    assert(list.tail < index); // wrong order

                    nodes[list.tail].next = index;
                    nodes[index] = .{
                        .next = 0,
                        .prev = list.tail,
                    };

                    list.tail = index;
                } else {
                    nodes[index] = .{
                        .next = 0,
                        .prev = 0xffff,
                    };

                    self.free = .{
                        .head = index,
                        .tail = index,
                    };
                }
            }

            /// Remove marked entities from the component array by swap removal.
            ///
            /// Entities are popped from the end of the array to fill spaces left
            /// by entities marked for removal. Each component array is moved
            /// separately to avoid having to load several locations at once
            /// leaving only the entity id array and hopefully the end
            /// of the component array in cache.
            pub fn commit(self: *Bucket, map: *const EntityMap) void {
                const es = self.entities();
                const nodes = @ptrCast([*]Node, es.ptr);
                const list = self.free orelse return;

                self.free = null;

                var newlen: u16 = self.len;
                var span: Free = list;
                var limit: u16 = newlen;

                var it = self.iterator();
                while (it.next()) |pair| {
                    span = list;
                    newlen = self.len;

                    loop: while (true) {
                        while (span.tail >= newlen) {
                            if (newlen == 0) break :loop;
                            const prev = nodes[span.tail].prev;
                            if (prev == 0xffff) break :loop;
                            span.tail = prev;
                        }

                        const size = layout.size[@enumToInt(pair.tag)];
                        const dst = pair.ptr + span.head * size;
                        const src = pair.ptr + (newlen - 1) * size;

                        @memcpy(dst, src, size);

                        const next = nodes[span.head].next;
                        span.head = next;

                        newlen -= 1;

                        if (next == 0) break;
                    }
                }

                newlen = self.len;
                span = list;

                loop: while (newlen > 0) : (limit -= 1) {
                    while (span.tail >= newlen) {
                        if (newlen == 0) break :loop;
                        const prev = nodes[span.tail].prev;
                        if (prev == 0xffff) break :loop;
                        span.tail = prev;
                    }

                    const index = span.head;
                    const next = nodes[index].next;
                    es[index] = es[newlen - 1];

                    if (index != newlen - 1) {
                        const pointer = map.getPtr(es[index]).?;
                        pointer.index = index;
                    }

                    span.head = next;

                    newlen -= 1;

                    if (next == 0) break;
                }

                self.len = newlen;
            }

            // -- DEINIT --

            pub fn deinit(self: *Bucket, gpa: Allocator) void {
                gpa.free(self.bytes);
                self.* = undefined;
            }
        };

        // -- DEINIT --

        pub fn deinit(self: *Self, gpa: Allocator) void {
            self.entities.deinit(gpa);

            var it = self.storage.valueIterator();
            while (it.next()) |bucket| bucket.deinit(gpa);
            self.storage.deinit(testing.allocator);
        }

        // -- private --

        const layout = blk: {
            const tmp = meta.fields(Spec);

            var fields = tmp[0..tmp.len].*;
            var alignment: [tmp.len]u8 = undefined;
            var size: [tmp.len]u8 = undefined;
            var set: [tmp.len]Type.EnumField = undefined;
            var split: u16 = 0;

            std.sort.sort(Type.StructField, &fields, {}, struct {
                pub fn lessThan(_: void, comptime lhs: Type.StructField, comptime rhs: Type.StructField) bool {
                    return lhs.alignment > rhs.alignment;
                }
            }.lessThan);

            for (fields) |field, index| {
                if (@sizeOf(field.field_type) > 0) split = index;
                alignment[index] = field.alignment;
                size[index] = @sizeOf(field.field_type);
                set[index] = .{
                    .name = field.name,
                    .value = index,
                };
            }

            split += 1;

            const Tag = @Type(.{ .Enum = .{
                .layout = .Auto,
                .fields = &set,
                .decls = &.{},
                .is_exhaustive = true,
                .tag_type = math.IntFittingRange(0, fields.len - 1),
            } });

            break :blk .{
                .fields = fields,
                .alignment = alignment,
                .size = size,
                .tag = Tag,
                .split = @as(comptime_int, split),
            };
        };
    };
}

test "alias" {
    const Data = struct {
        x: u32,
    };

    const DB = Model(Data);

    var db: DB = .{};
    defer db.deinit(testing.allocator);

    const ctx = db.context(&.{});

    const e = ctx.new();

    try ctx.update(testing.allocator, e, struct { x: u32 = 4 }, .{});

    var it = ctx.query(struct { x: u32 });

    while (it.next()) |result| {
        const p = result.pointers;
        for (p.x[0..result.bucket.len]) |x| try testing.expectEqual(@as(u32, 4), x);
    }

    const otx = db.context(&.{.{ .component = .x, .alias = .foo }});

    var itt = otx.query(struct { foo: u32 });

    while (itt.next()) |result| {
        const p = result.pointers;
        for (p.foo[0..result.bucket.len]) |x| try testing.expectEqual(@as(u32, 4), x);
    }
}

test "migrate entities" {
    const Data = struct {
        x: u32,
        y: u8,
    };

    const DB = Model(Data);

    var db: DB = .{};
    defer db.deinit(testing.allocator);

    const default = db.context(&.{});

    var es: [8]Entity = undefined;

    for (es) |*e, index| {
        e.* = default.new();
        try default.update(testing.allocator, e.*, struct { x: u32 }, .{
            .x = @intCast(u32, index + 8),
        });
    }

    for (es[4..]) |e, index| {
        try default.update(testing.allocator, e, struct { y: u8 }, .{
            .y = @intCast(u8, index + 8),
        });
    }

    var it = default.query(struct { x: u32 });
    while (it.next()) |result| {
        try testing.expectEqual(@as(usize, 4), result.bucket.len);
        const p = result.pointers;

        if (result.bucket.type.has(.y)) {
            try testing.expectEqualSlices(u32, &.{ 12, 13, 14, 15 }, p.x[0..result.bucket.len]);
            try testing.expectEqualSlices(u8, &.{ 8, 9, 10, 11 }, result.bucket.items(.y));
        } else {
            try testing.expectEqualSlices(u32, &.{ 8, 9, 10, 11 }, p.x[0..result.bucket.len]);
        }
    }

    for (es) |e, index| {
        const pointer = db.entities.get(e).?;
        const bucket = db.storage.getPtr(pointer.type).?;
        const value = bucket.items(.x)[pointer.index];
        try testing.expectEqual(@intCast(u32, index + 8), value);

        if (pointer.type.has(.y)) {
            const small = bucket.items(.y)[pointer.index];
            try testing.expectEqual(@intCast(u8, index + 4), small);
        }
    }
}

test "simd" {
    const Data = struct {
        position: Vec3 align(16),
        velocity: Vec3 align(16),

        pub const Vec3 = extern struct { x: f32, y: f32, z: f32 };
    };

    const DB = Model(Data);

    var db: DB = .{};
    defer db.deinit(testing.allocator);

    const default = db.context(&.{});

    var es: [32]Entity = undefined;

    for (es) |*e, index| {
        const i = 1 / @intToFloat(f32, index);

        const point = .{ .x = i, .y = i, .z = i };

        e.* = default.new();
        try default.update(testing.allocator, e.*, Data, .{
            .position = point,
            .velocity = point,
        });
    }

    var it = default.query(struct {
        position: *Data.Vec3,
        velocity: Data.Vec3,
    });

    while (it.next()) |result| {
        const p = result.pointers;

        const f32x8 = @Vector(8, f32);

        var pos = @ptrCast([*]f32, p.position);
        var vel = @ptrCast([*]const f32, p.velocity);
        const len = result.bucket.len * 3;

        var index: u16 = 0;
        while (len - index > 8) : (index += 8) {
            pos[0..8].* = @as(f32x8, pos[0..8].*) + @as(f32x8, vel[0..8].*);

            pos += 8;
            vel += 8;
        }

        for (vel[0 .. len - index]) |v, i| pos[i] += v;
    }

    const bucket = db.storage.getPtr(DB.Archetype.fromType(Data)).?;
    const pos = bucket.items(.position);
    const vel = bucket.items(.velocity);

    for (pos) |p, index| {
        const v = vel[index];

        try testing.expectApproxEqAbs(p.x, v.x + v.x, 0.00001);
        try testing.expectApproxEqAbs(p.y, v.y + v.y, 0.00001);
        try testing.expectApproxEqAbs(p.z, v.z + v.z, 0.00001);
    }
}
