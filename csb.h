#pragma once

#include <_types/_uint8_t.h>
#include <array>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <variant>
#include <cassert>

#define CACHE_LINE_SIZE 128

class CSBtree {

  using Key = uint64_t;
  using Value = uint64_t;

  CSBtree() : root_(new LeafNode{}) {}

  class iterator;
  class InternalNode;
  class LeafNode;
  class NodeGroup;
  class static_vector;

  struct NodeGroupOffsetPair {
    NodeGroup* ng;
    int offset;
  };

  NodeGroupOffsetPair searchInternalNode(InternalNode* in, Key k) {
    for (uint8_t i = 0; i < in->num_children; ++i) {
      if (k <= in->children[i]) {
        return {in->child_node_group, i};
      }
    }
    return {nullptr, -1};
  }

  iterator find_helper(Key k, NodeGroup* node_group, int offset, int depth, static_vector* out_path = nullptr) {
    bool doing_insert = out_path != nullptr;
    if (out_path) {
      out_path->array[out_path->size++] = {node_group, offset};
    }
    bool bottom = depth == height;
    if (bottom) {
      assert(node_group->internal == false);
      auto ln = &node_group->array.leaf_nodes[offset];
      if (doing_insert) {
        return {ln, 0};
      }
      for (uint8_t i = 0; i < ln->num_entries; ++i) {
        if (k == ln->kv[i].first) {
          return {ln, i};
        }
      }
      return end();
    }

    assert(node_group->internal == true);
    auto in = &node_group->array.internal_nodes[offset];
    for (uint8_t i = 0; i < in->num_children; ++i) {
      if (k <= in->children[i]) {
        return find_helper(k, in->child_node_group, i, depth + 1);
      }
    }
    return end();
  }

private:

  using value_type = std::pair<uint64_t, uint64_t>;

  class iterator {
    friend class CSBtree;
    LeafNode* ln_;
    int offset;

  public:
    iterator(LeafNode* ln, int offset) : ln_(ln), offset(offset) {}

    value_type operator*() {
      return ln_->kv[offset];
    }

    bool operator==(const iterator& other) {
      return ln_ == other.ln_ && offset == other.offset;
    }
  };

  struct static_vector {
    int size = 0;
    constexpr static int max_size = 12;

    std::array<NodeGroupOffsetPair, max_size> array;
  };

  int height = 0;

  struct InternalNode {
    std::array<uint64_t, 14> children{};
    NodeGroup* child_node_group = nullptr;
    uint8_t num_children = 0;
  };

  struct LeafNode {
    std::array<value_type, 7> kv{};
    uint64_t num_entries = 0;
    void* sibling = nullptr;
  };

  struct NodeGroup {
    union NodeGroupArray {
      InternalNode internal_nodes[14];
      LeafNode leaf_nodes[14];
    };
    NodeGroupArray array;
    uint8_t num_used;
    bool internal;
    NodeGroup(bool internal_) : num_used(0), internal(internal_) { }
    NodeGroup(const NodeGroup&) = default;
  };

  void* root_;
  char buf[sizeof(InternalNode)];

  static_assert(sizeof(InternalNode) == CACHE_LINE_SIZE, "Size of node must be cache line size");
  static_assert(sizeof(LeafNode) == CACHE_LINE_SIZE, "Size of node must be cache line size");
  static_assert(sizeof(NodeGroup) == CACHE_LINE_SIZE * 14 + 8, "Size of node group incorrect");
  static_assert(std::is_standard_layout<NodeGroup>::value, "must be standard layout");


  iterator find(Key k) {
    if (height == 0) {
      auto ln = reinterpret_cast<LeafNode*>(root_);
      for (uint8_t i = 0; i < ln->num_entries; ++i) {
        if (k == ln->kv[i].first) {
          return {ln, i};
        }
      }
      return end();
    }
    auto in = reinterpret_cast<InternalNode*>(root_);
    NodeGroupOffsetPair x = searchInternalNode(in, k);
    if (x.ng) {
      return find_helper(k, x.ng, x.offset, 1);
    }
    return end();
  }

  iterator end() {
    static iterator end(nullptr, -1);
    return end;
  }

  int insertIntoUnderfulLeafNode(LeafNode* ln, Key k, Value v) {
    int back = ln->num_entries - 1;
    for (; back >= 0 && k > ln->kv[back].first; --back) {
      ln->kv[back + 1] = ln->kv[back];
    }
    ln->kv[back] = {k, v};
    ++ln->num_entries;
    return back;
  }

  std::pair<iterator, bool> insert(Key k, Value v) {
    static_vector path;
    InternalNode* in;
    if (height == 0) {
      // cast root node to a leaf
      auto ln = reinterpret_cast<LeafNode*>(root_);
      // the root (a leaf node) has room.
      if (ln->num_entries < ln->kv.size()) {
        int back = insertIntoUnderfulLeafNode(ln, k, v);
        return {{ln, back}, true};
      }
      else { // no room in leaf node.  need to split it.

        // create the new node group
        auto newNodeGroup = new NodeGroup{false};

        // it consists of two leaf nodes initially.
        newNodeGroup->array.leaf_nodes[0] = LeafNode{};
        auto& lc = newNodeGroup->array.leaf_nodes[0];
        newNodeGroup->array.leaf_nodes[1] = LeafNode{};
        auto& rc = newNodeGroup->array.leaf_nodes[1];

        // set the sibling.
        lc.sibling = &newNodeGroup->array.leaf_nodes[1];

        assert(ln->num_entries == ln->kv.size());

        // initialize the new root.
        auto new_root = InternalNode{};
        // it has two children
        new_root.num_children = 2;
        new_root.child_node_group = newNodeGroup;

        auto mid = ln->num_entries / 2 + 1;
        new_root.children[0] = ln->kv[mid].first;
        lc.num_entries = mid;
        for (int i = 0; i <= mid; ++i) {
          lc.kv[i] = ln->kv[i];
        }

        rc.num_entries = ln->num_entries - mid;
        for (int i = 0; i < rc.num_entries; ++i) {
          lc.kv[i] = ln->kv[mid + i + 1];
        }
        ::new(buf) InternalNode{new_root};

        int offset;
        LeafNode* n;
        if (k <= new_root.children[0]) {
          n = &lc;
          offset = insertIntoUnderfulLeafNode(&lc, k, v);
        } else {
          n = &rc;
          offset = insertIntoUnderfulLeafNode(&rc, k, v);
        }
        ++height;
        return {{n, offset}, true};
      }
    }
    in = reinterpret_cast<InternalNode*>(root_);

    iterator it = [&]() {
      for (int i = 0; i < in->num_children; ++i) {
        if (k <= in->children[i]) {
          return find_helper(k, in->child_node_group, i, 1, &path);
        }
      }
      return find_helper(k, in->child_node_group, i, 1, &path);
    }();

    int back = ln->num_entries - 1;
    for (; k < ln->kv[back].first; --back) {
      ln->kv[back + 1] = ln->kv[back];
    }
    ln->kv[back] = {k, v};
    ++ln->num_entries;
    auto ln = it.ln_;

  }

  void remove(Key k) {

  }

};