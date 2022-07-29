const std = @import("std");
const mem = std.mem;
const meta = std.meta;
const math = std.math;
const testing = std.testing;
const assert = std.debug.assert;
const todo = std.debug.todo;

const Type = std.builtin.Type;
const Allocator = std.mem.Allocator;

fn Decompose(comptime Data: type) type {
    comptime {
        const tmp = meta.fields(Data);
        var fields = tmp[0..tmp.len].*;
        var alignment: [fields.len]u8 = undefined;
        var size: [fields.len]u8 = undefined;
        var set: [fields.len]Type.EnumField = undefined;
        var split: usize = 0;

        std.sort.sort(Type.StructField, &fields, {}, struct {
            pub fn lessThan(_: void, comptime lhs: Type.StructField, comptime rhs: Type.StructField) bool {
                const al = @maximum(@sizeOf(lhs.field_type), lhs.alignment);
                const ar = @maximum(@sizeOf(rhs.field_type), rhs.alignment);
                return al > ar;
            }
        }.lessThan);

        for (fields) |field, index| {
            if (@sizeOf(field.field_type) > 0) {
                alignment[index] = field.alignment;
                split = index;
            } else {
                alignment[index] = 0;
            }

            size[index] = @sizeOf(field.field_type);
            set[index] = .{
                .name = field.name,
                .value = index,
            };
        }

        const tag = @Type(.{ .Enum = .{
            .layout = .Auto,
            .fields = &set,
            .decls = &.{},
            .is_exhaustive = true,
            .tag_type = math.IntFittingRange(0, fields.len - 1),
        } });

        return struct {
            pub const fields = fields;
            pub const alignment = alignment;
            pub const size = size;
            pub const tag = tag;
            pub const split = @as(comptime_int, split);
        };
    }
}

/// Entity identifier
pub const Entity = enum(u32) { _ };

pub fn Archetype(comptime Data: type) type {
    const layout = Decompose(Data);
    return struct {
        bitset: Set = empty,

        pub const Set = [slots]u32;
        pub const Int = u32;
        pub const Shift = u5;
        pub const empty = mem.zeroes(Set);

        const slots = @maximum(1, layout.fields.len >> 5);

        pub const Tag = layout.tag;
        const Self = @This();

        fn bit(tag: Tag) u32 {
            return @as(Int, 1) << @truncate(Shift, @as(u32, @enumToInt(tag)));
        }

        fn slot(tag: Tag) u32 {
            return @as(u32, @enumToInt(tag)) >> @bitSizeOf(Shift);
        }

        // TODO: check that this works correctly with result location semantics

        /// Produce a new archetype with the given component set.
        pub fn add(self: Self, tag: Tag) Self {
            var set = self;

            set.bitset[slot(tag)] |= bit(tag);

            return set;
        }

        /// Produce a new archetype without the given component.
        pub fn remove(self: Self, tag: Tag) Self {
            var set = self;

            set.bitset[slot(tag)] &= ~bit(tag);

            return set;
        }

        /// Test if the archetype has a given component bit set.
        pub fn has(self: Self, tag: Tag) bool {
            return self.bitset[slot(tag)] & bit(tag) == bit(tag);
        }

        /// Merge two archetype bitsets.
        pub fn merge(self: Self, other: Self) Self {
            var set = self;
            for (other.bitset) |cell, i| {
                set.bitset[i] |= cell;
            }

            return set;
        }

        /// Test if the given archetype is a superset of the other.
        pub fn contains(self: Self, other: Self) bool {
            for (other.bitset) |cell, i| {
                if (self.bitset[i] & cell != cell) return false;
            }

            return true;
        }

        /// Create an archetype from a slice of component tags.
        pub fn fromList(tags: []const Tag) Self {
            var tmp: Self = .{};

            for (tags) |tag| tmp = tmp.add(tag);

            return tmp;
        }

        /// Create an archetype from field names within a given struct type.
        pub inline fn fromType(comptime T: type) Self {
            comptime {
                const info = @typeInfo(T).Struct;

                var tmp: Self = .{};

                for (info.fields) |field| {
                    tmp = tmp.add(@field(Tag, field.name));
                }

                return tmp;
            }
        }

        /// Get the type of a component value given the component tag.
        pub fn TypeOf(comptime tag: Tag) type {
            return layout.fields[@enumToInt(tag)].field_type;
        }

        /// Return an iterator over currently active component tags in the
        /// order of decending alignment.
        pub fn iterator(self: *const Self) Iterator {
            return .{ .type = self };
        }

        pub const Iterator = struct {
            type: *const Self,
            offset: u4 = 0,
            mask: u32 = 0,

            /// Return the next component tag present within the archetype.
            pub fn next(self: *Iterator) ?Tag {
                for (self.type.bitset[self.offset..]) |cell| {
                    const int = @ctz(u32, cell & ~self.mask);
                    if (int != 32) {
                        const index = @shlExact(@as(u32, 1), @intCast(Shift, int));
                        self.mask |= index;
                        const bits = @intCast(meta.Tag(Tag), 32 * @as(u32, self.offset));
                        const tag = @intToEnum(Tag, int + bits);
                        return tag;
                    }

                    self.mask = 0;
                    self.offset += 1;
                }

                return null;
            }
        };

        pub fn backwardIterator(self: *const Self) BackwardIterator {
            return .{ .type = self };
        }

        pub const BackwardIterator = struct {
            type: *const Self,
            offset: u4 = slots - 1,
            mask: u32 = 0,

            pub fn next(self: *BackwardIterator) ?Tag {
                const len = self.type.bitset.len - 1;
                while (true) {
                    const cell = @clz(u32, self.type.bitset[len - self.offset] & ~self.mask);
                    if (cell != 32) {
                        const int = @intCast(Shift, 31 - cell);
                        const index = @shlExact(@as(u32, 1), int);
                        self.mask |= index;
                        const bits = @intCast(meta.Tag(Tag), 32 * @as(u32, self.offset));
                        const tag = @intToEnum(Tag, int + bits);
                        return tag;
                    }

                    if (self.offset == 0) return null;

                    self.mask = 0;
                    self.offset -= 1;
                }
            }
        };
    };
}

test "Archetype iterators" {
    const Data = struct { x: u32, y: f32, z: u8, w: u128 };

    const a = Archetype(Data);
    const b = Archetype(Data);
    comptime assert(a == b);

    const T = Archetype(Data);
    const archetype = T.fromType(Data);

    var it = archetype.iterator();
    for ([_]T.Tag{ .w, .x, .y, .z }) |tag| {
        const found = it.next() orelse return error.Unexpected;

        try testing.expectEqual(tag, found);
    }

    var bi = archetype.backwardIterator();
    for ([_]T.Tag{ .z, .y, .x, .w }) |tag| {
        const found = bi.next().?;

        try testing.expectEqual(tag, found);
    }
}

pub fn BucketUnmanaged(comptime Data: type) type {
    return struct {
        bucket: Bucket(Data),
        const Self = @This();

        pub fn entities(self: *Self) []Entity {
            return self.bucket.entities();
        }

        pub fn setCapacity(self: *Self, gpa: Allocator, new_capacity: u16) !void {
            const alignment = self.bucket.alignment();
            const bytes = self.bucket.bytesOf(new_capacity);

            if (gpa.resize(self.bytes, bytes)) |new_bytes| {
                var new = self.*;
                new.bytes = new_bytes;
                new.capacity = new_capacity;
                self.copyBackwardsTo(new);
                return;
            }

            const new_bytes = try gpa.allocBytes(alignment, bytes, 0, @returnAddress());

            if (self.len == 0) {
                gpa.free(self.bytes);
                self.bytes = new_bytes;
                self.capacity = new_capacity;
                return;
            }

            var new = self.*;
            new.bytes = new_bytes;
            new.capacity = new_capacity;

            self.copyTo(new);
            gpa.free(self.bytes);

            self.* = new;
        }

        pub fn deinit(self: *Self, gpa: Allocator) void {
            gpa.free(self.bucket.bytes);
            self.* = .{};
        }
    };
}

pub fn Bucket(comptime Data: type) type {
    const layout = Decompose(Data);
    const natural_alignment = blk: {
        var tmp = true;
        for (layout.size) |size, index| {
            tmp = size == layout.alignment[index] and tmp;
        }

        break :blk tmp;
    };
    return struct {
        type: Archetype(Data),
        capacity: u16 = 0,
        bytes: []u8 = &.{},
        free: Free = .{},
        len: u16 = 0,

        const Self = @This();

        pub fn entities(self: Self) []Entity {
            const offset = self.bytes.ptr + (self.bytes.len - @sizeOf(Entity) * self.capacity);
            return @ptrCast([*]Entity, @alignCast(@alignOf(Entity), offset))[0..self.len];
        }

        pub fn alignment(archetype: Archetype(Data)) u29 {
            var it = archetype.iterator();
            const first = it.next() orelse return @alignOf(Entity);
            return layout.alignment[@enumToInt(first)];
        }

        pub fn sizeOf(archetype: Archetype(Data), new_capacity: u16) usize {
            var size: usize = 0;

            var it = archetype.iterator();
            while (it.next()) |tag| {
                const al = layout.alignment[@enumToInt(tag)];
                size = mem.alignForward(size, al) +
                    layout.size[@enumToInt(tag)] * new_capacity;
            }

            return mem.alignForward(size, @alignOf(Entity)) + @sizeOf(Entity) * new_capacity;
        }

        pub fn push(self: *Self, entries: u16) error{Capacity}!u16 {
            if (@as(u32, self.len) + entries > self.capacity) return error.Capacity;
            defer self.len += 1;
            return self.len;
        }

        pub fn copyTo(self: Self, other: Self) void {
            assert(self.type == other.type);
            assert(self.bytes.len <= other.bytes.len);

            var si = self.iterator();
            var oi = other.iterator();

            mem.copy(Entity, other.entities(), self.entities());

            while (si.next()) |src| {
                const dst = oi.findNext(src.tag);
                const len = @as(usize, layout.size[@enumToInt(src.tag)]) * self.len;

                @memcpy(dst.ptr, src.ptr, len);
            }
        }

        pub fn items(self: Self, comptime tag: Archetype(Data).Tag) []Archetype(Data).TypeOf(tag) {
            return @ptrCast(
                [*]Archetype(Data).TypeOf(tag),
                self.iterator().findNext(tag).?.ptr,
            )[0..self.capacity];
        }

        /// Move an entity from the current bucket to anoher.
        ///
        /// note: the source bucket is left sparse after moving the entity thus a call
        ///       to `.commit` needs to be issued before iterating over the contents.
        pub fn move(self: *Self, dst_index: u16, other: Self, src_index: u16) void {
            var si = self.iterator();
            var oi = other.iterator();

            while (si.next()) |src| {
                const dst = oi.findNext(src.tag).?;
                const size: usize = layout.size[@enumToInt(src.tag)];
                @memcpy(dst.ptr + dst_index * size, src.ptr + src_index * size, size);
            }

            other.entities()[dst_index] = self.entities()[src_index];
            self.remove(src_index);
        }

        pub fn iterator(self: *const Self) Iterator {
            return .{
                .capacity = self.capacity,
                .type = self.type.iterator(),
                .ptr = self.bytes.ptr,
            };
        }

        pub const Iterator = struct {
            capacity: u16,
            type: Archetype(Data).Iterator,
            ptr: [*]u8,

            pub fn next(self: *Iterator) ?Pair {
                const tag = self.type.next() orelse return null;
                const index = @enumToInt(tag);
                const offset = mem.alignForward(@ptrToInt(self.ptr), layout.alignment[index]) -
                    @ptrToInt(self.ptr);

                self.ptr += offset;

                defer self.ptr += self.capacity * layout.size[index];

                return Pair{ .tag = tag, .ptr = self.ptr };
            }

            pub fn findNext(self: *Iterator, tag: Archetype(Data).Tag) ?Pair {
                while (self.next()) |found| {
                    if (found.tag == tag) return found;
                }

                return null;
            }
        };

        pub fn copyBackwardsTo(self: Self, other: Self) void {
            assert(self.type == other.type);
            assert(self.bytes.len <= other.bytes.len);

            var si = self.backwardIterator();
            var oi = other.backwardIterator();

            mem.copyBackwards(Entity, other.entities(), self.entities());

            while (si.next()) |src| {
                const dst = oi.findNext(src.tag);
                const len = @as(usize, layout.size[@enumToInt(src.tag)]) * self.len;

                mem.copyBackwards(u8, dst.ptr[0..len], src.ptr[0..len]);
            }
        }

        pub fn backwardIterator(self: *const Self) BackwardIterator {
            if (natural_alignment) {
                return .{
                    .capacity = self.capacity,
                    .offset = @ptrToInt(self.entities().ptr) - @ptrToInt(self.bytes.ptr),
                    .type = self.type.backwardIterator(),
                    .ptr = self.bytes.ptr,
                };
            }
            return .{
                .capacity = self.capacity,
                .type = self.type.backwardIterator(),
                .ptr = self.bytes.ptr,
            };
        }

        pub const Pair = struct {
            tag: Archetype(Data).Tag,
            ptr: [*]u8,
        };

        pub const BackwardIterator = if (natural_alignment) struct {
            capacity: u16,
            offset: usize,
            type: Archetype(Data).BackwardIterator,
            ptr: [*]u8,

            pub fn next(self: *BackwardIterator) ?Pair {
                const tag = self.type.next() orelse {
                    assert(self.offset == 0);
                    return null;
                };

                const index = @enumToInt(tag);
                self.offset -= layout.size[index] * self.capacity;

                return Pair{ .ptr = self.ptr + self.offset, .tag = tag };
            }
        } else struct {
            capacity: u16,
            type: Archetype(Data).BackwardIterator,
            ptr: [*]u8,

            pub fn next(self: *BackwardIterator) ?Pair {
                var tmp: Iterator = .{
                    .capacity = self.capacity,
                    .type = self.type.type.iterator(),
                    .ptr = self.ptr,
                };

                const tag = self.type.next() orelse return null;

                return tmp.findNext(tag).?;
            }
        };

        const Free = struct {
            head: u16 = 0xffff,
            tail: u16 = 0,

            pub fn clear(self: *Free) void {
                self.* = .{};
            }

            pub fn isEmpty(self: Free) bool {
                return self.head > self.tail;
            }
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

            if (!self.free.isEmpty()) {
                assert(self.free.tail < index); // wrong order

                nodes[self.free.tail].next = index;
                nodes[index] = .{
                    .next = 0,
                    .prev = self.free.tail,
                };

                self.free.tail = index;
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
        pub fn commit(self: *Self, comptime Map: type, map: *const Map) void {
            const es = self.entities();
            const nodes = @ptrCast([*]Node, es.ptr);

            if (self.free.isEmpty()) return;

            const list = self.free;

            self.free.clear();

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

                    const size: usize = layout.size[@enumToInt(pair.tag)];
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
    };
}

test "Bucket.iterator" {
    const Data = struct { x: u32, y: f32, z: u8, w: u128 };

    const archetype = comptime Archetype(Data).fromType(Data);

    const size = comptime Bucket(Data).sizeOf(archetype, 32);
    const alignment = comptime Bucket(Data).alignment(archetype);
    var backing: [size]u8 align(alignment) = undefined;

    var a: Bucket(Data) = .{
        .type = archetype,
        .bytes = &backing,
        .capacity = 32,
    };

    const w = 0;
    const x = @sizeOf(u128) * 32;
    const y = x + @sizeOf(u32) * 32;
    const z = y + @sizeOf(f32) * 32;

    const base = @ptrToInt(&backing);

    var it = a.iterator();
    for ([_]usize{ w, x, y, z }) |offset| {
        const found = it.next().?;

        try testing.expectEqual(offset, @ptrToInt(found.ptr) - base);
    }

    var bi = a.backwardIterator();
    for ([_]usize{ z, y, x, w }) |offset| {
        const found = bi.next().?;

        try testing.expectEqual(offset, @ptrToInt(found.ptr) - base);
    }
}

test "Bucket.iterator alignment" {
    const Data = struct {
        x: u32 align(8),
        y: f32 align(8),
        z: u8,
    };

    const archetype = comptime Archetype(Data).fromType(Data);

    const size = comptime Bucket(Data).sizeOf(archetype, 31);
    const alignment = comptime Bucket(Data).alignment(archetype);
    var backing: [size]u8 align(alignment) = undefined;

    var a: Bucket(Data) = .{
        .type = archetype,
        .bytes = &backing,
        .capacity = 31,
    };

    const x = 0;
    const y = 4 + @sizeOf(u32) * 31;
    const z = y + @sizeOf(f32) * 31;

    const base = @ptrToInt(&backing);

    var bi = a.backwardIterator();
    for ([_]usize{ z, y, x }) |offset| {
        const found = bi.next().?;

        try testing.expectEqual(offset, @ptrToInt(found.ptr) - base);
    }
}

pub fn Model(comptime Data: type) type {
    const layout = Decompose(Data);
    return struct {
        entities: EntityMap = .{},
        buckets: BucketMap = .{},
        count: u32 = 0,

        pub const EntityMap = std.hash_map.AutoHashMapUnmanaged(Entity, Pointer);
        pub const BucketMap = std.hash_map.AutoHashMapUnmanaged(Archetype(Data), Bucket(Data));
        pub const Pointer = struct {
            index: u16,
            type: Archetype(Data),
        };

        const Self = @This();

        pub const CreateError = error{
            /// Failed to allocate memory for the entity hashmap.
            OutOfMemory,
            /// Missing bucket for the given archetype.
            MissingBucket,
            /// Bucket has reached it's capacity limits.
            Capacity,
            /// Ouf of slots.
            OutOfEntitySlots,
        };

        /// Create a new `Entity`.
        pub fn create(self: *Self, gpa: Allocator, comptime T: type, value: T) CreateError!Entity {
            var limit: u32 = 0;
            var count: u32 = self.count;
            defer self.count = count;

            while (true) {
                const entity = @intToEnum(Entity, count);

                if (self.entities.contains(entity)) {
                    limit += 1;
                    count +%= 1;
                    if (limit == 0xffff) break;
                    continue;
                }

                const archetype = Archetype(Data).fromType(T);
                const target = self.buckets.getPtr(archetype) orelse return error.MissingBucket;

                const index = try target.push(1);
                errdefer target.len -= 1;

                try self.entities.put(gpa, entity, .{
                    .index = index,
                    .type = archetype,
                });

                target.entities()[index] = entity;

                var it = target.iterator();

                inline for (layout.fields) |field| {
                    if (@hasField(T, field.name)) {
                        const tag = @field(Archetype(Data).Tag, field.name);
                        const size: usize = comptime layout.size[@enumToInt(tag)];

                        const dst = it.findNext(tag).?;
                        const offset = index * size;

                        @memcpy(dst.ptr + offset, mem.asBytes(&@field(value, field.name)), size);
                    }
                }

                return entity;
            }

            return error.OutOfEntitySlots; // 4GiB of just entity ids? really?
        }

        pub const UpdateError = error{
            /// Missing bucket for the given archetype.
            MissingBucket,
            /// The target Bucket has reached it's capacity limits.
            Capacity,
        };

        pub const RegisterError = error{
            OutOfMemory,
        };

        pub fn register(self: *Self, gpa: Allocator, bucket: Bucket(Data)) RegisterError!void {
            try self.buckets.putNoClobber(gpa, bucket.type, bucket);
        }

        pub fn update(self: Self, entity: Entity, comptime T: type, value: T) UpdateError!void {
            const pointer = self.entities.getPtr(entity).?;
            const archetype = pointer.type.merge(Archetype(Data).TypeOf(T));
            const target = self.buckets.getPtr(archetype) orelse return error.MissingBucket;

            if (archetype != pointer.type) {
                const origin = self.buckets.getPtr(pointer.type).?;
                const index = try target.push(1);

                origin.move(index, target, pointer.index);

                pointer.index = index;
                pointer.type = archetype;
            }

            var it = target.iterator();

            inline for (layout.fields) |field| {
                if (@hasField(T, field.name) and @sizeOf(field.field_type) != 0) {
                    const tag = @field(Archetype(Data).Tag, field.name);
                    const size: usize = comptime layout.size[@enumToInt(tag)];

                    const dst = it.findNext(tag).?;
                    const offset = pointer.index * size;

                    @memcpy(dst.ptr + offset, &@field(value, field.name), size);
                }
            }
        }

        pub fn query(self: *Self, comptime spec: type) Query(spec) {
            return .{
                .model = self,
                .buckets = self.buckets.iterator(),
            };
        }

        pub fn Query(comptime spec: type) type {
            return struct {
                model: *Self,
                buckets: BucketMap.Iterator,

                const archetype = Archetype(Data).fromType(spec);

                pub const Result = struct {
                    bucket: *Bucket(Data),
                    ptr: Pointers,
                    len: u16,

                    const Tag = meta.FieldEnum(Pointers);

                    fn Item(comptime com: Tag) type {
                        const info = @typeInfo(meta.fieldInfo(Pointers, com).field_type).Pointer;
                        if (info.is_const) {
                            return []const info.child;
                        } else {
                            return []info.child;
                        }
                    }

                    pub inline fn items(self: Result, comptime com: Tag) Item(com) {
                        return @field(self.ptr, @tagName(com))[0..self.len];
                    }

                    pub const Pointers = blk: {
                        var fields: [layout.fields.len]Type.StructField = undefined;
                        var result: spec = undefined;

                        var index: u16 = 0;
                        for (layout.fields) |field| {
                            if (@hasField(spec, field.name)) {
                                const T = @TypeOf(@field(result, field.name));
                                fields[index] = field;
                                if (T == field.field_type) {
                                    fields[index].field_type = [*]const field.field_type;
                                } else if (T == *field.field_type) {
                                    fields[index].field_type = [*]field.field_type;
                                } else @compileError("");
                                index += 1;
                            }
                        }

                        break :blk @Type(.{ .Struct = .{
                            .layout = .Auto,
                            .fields = fields[0..index],
                            .decls = &.{},
                            .is_tuple = false,
                        } });
                    };
                };

                fn pointers(bucket: *Bucket(Data)) Result.Pointers {
                    var result: Result.Pointers = undefined;

                    var it = bucket.iterator();

                    inline for (meta.fields(Result.Pointers)) |field| {
                        const tag = @field(Archetype(Data).Tag, field.name);
                        const alignment = @alignOf(Archetype(Data).TypeOf(tag));
                        const src = it.findNext(tag).?;
                        @field(result, field.name) = @ptrCast(field.field_type, @alignCast(alignment, src.ptr));
                    }

                    return result;
                }

                pub fn next(self: *@This()) ?Result {
                    var bucket = self.buckets.next() orelse return null;

                    while (!bucket.key_ptr.contains(archetype)) {
                        bucket = self.buckets.next() orelse return null;
                    }

                    const p = pointers(bucket.value_ptr);
                    bucket.value_ptr.commit(EntityMap, &self.model.entities);

                    return Result{
                        .bucket = bucket.value_ptr,
                        .ptr = p,
                        .len = bucket.value_ptr.len,
                    };
                }
            };
        }

        pub fn deinit(self: *Self, gpa: Allocator) void {
            self.entities.deinit(gpa);
            self.buckets.deinit(gpa);
        }
    };
}

test "Model.query" {
    const Data = struct { x: u32, y: f32, z: u8, w: u128 };
    const Subset = struct { x: u32, y: f32 };

    var model: Model(Data) = .{};
    defer model.entities.deinit(testing.allocator);
    defer model.buckets.deinit(testing.allocator);

    const archetype = comptime Archetype(Data).fromType(Subset);
    const size = comptime Bucket(Data).sizeOf(archetype, 32); // entries
    const alignment = comptime Bucket(Data).alignment(archetype); // required alignment

    var backing: [size]u8 align(alignment) = undefined;

    var bucket = .{
        .type = archetype,
        .bytes = &backing,
        .capacity = 32,
    };

    try model.buckets.put(testing.allocator, bucket.type, bucket);

    const entity = try model.create(testing.allocator, Subset, .{
        .x = 42,
        .y = 0.42,
    });

    var it = model.query(struct {
        x: *u32,
        y: f32,
    });

    while (it.next()) |result| {
        for (result.ptr.y[0..result.bucket.len]) |y, i| {
            _ = y;
            result.ptr.x[i] = 32;
            try testing.expectEqual(entity, result.bucket.entities()[i]);
        }
    }
}
