// Copyright 2023 Yuxuan Chen
//
// Permission is hereby granted, free of charge, to any person obtaining a copy of this software
// and associated documentation files (the “Software”), to deal in the Software without
// restriction, including without limitation the rights to use, copy, modify, merge, publish,
// distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the
// Software is furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all copies or
// substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING
// BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
// DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

use im::Vector;

/// DiGraph implemented with immutable vector (RRB).

#[derive(Copy, Clone)]
pub enum Direction {
    Outgoing = 0,
    Incoming = 1,
}

const OUTGOING: usize = Direction::Outgoing as usize;
const INCOMING: usize = Direction::Incoming as usize;

pub type IdType = u32;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct NodeId(IdType);
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct EdgeId(IdType);

// Sentinel to end linked lists.
const INVALID: IdType = IdType::MAX;

/// Representation of a Node or a vacant spot if it's found as a part of unused_nodes. When a node
/// is present, the edges array stores pointers to heads of two linked lists.
#[derive(Clone)]
struct Node<NW: Clone> {
    weight: Option<NW>,
    edges: [IdType; 2],
}

impl<NW: Clone> Node<NW> {
    fn new(weight: NW) -> Self {
        Self {
            weight: Some(weight),
            edges: [INVALID, INVALID],
        }
    }

    fn weight(&self) -> &NW {
        self.weight.as_ref().unwrap()
    }
}

/// Because edges are accessible from both ends, each edge is considered an element of two linked
/// lists. One originated from each direction. Edges themselves contain data used for two doubly
/// linked lists representing their membership of [from, to] node's [out, in] adjacency lists.
#[derive(Clone)]
struct Edge<EW: Clone> {
    weight: Option<EW>,
    from: NodeId,
    to: NodeId,
    /// next[OUTGOING] is next in the chain when the edge is a part of a successor list.
    /// next[INCOMING] is next in the chain when the edge is a part of a predecessor list.
    next: [IdType; 2],
    /// prev[OUTGOING] is previous in the chain when the edge is a part of a successor list.
    /// prev[INCOMING] is previous in the chain when the edge is a part of a predecessor list.
    prev: [IdType; 2],
}

impl<EW: Clone> Edge<EW> {
    fn new(weight: EW, from: NodeId, to: NodeId) -> Self {
        Self {
            weight: Some(weight),
            from,
            to,
            next: [INVALID, INVALID],
            prev: [INVALID, INVALID],
        }
    }

    fn weight(&self) -> &EW {
        self.weight.as_ref().unwrap()
    }
}

/// Contraray to its name, `ImmutableGraph` has mutable semantics. The immutable bits of it are the
/// underlying data structure that backs the storage of the nodes and edges, which makes it trivial
/// to copy. This is useful in many cases: e.g. A graph building process that requires bookkeeping
/// intermediate steps, or algorithms that requires back tracking. `NodeId`s and `EdgeId`s of this
/// graph is stable for each `ImmutableGraph` object and cloned copies. (i.e. The indices into the
/// rest of the graph do not change when nodes and edges are removed from the graph.)
#[derive(Clone)]
pub struct ImmutableGraph<NW: Clone, EW: Clone> {
    /// By using im::Vector, the internal structure of this immutable graph is O(1) copy.
    nodes: Vector<Node<NW>>,
    edges: Vector<Edge<EW>>,
    unused_node: IdType,
    unused_edge: IdType,
}

impl<NW: Clone, EW: Clone> ImmutableGraph<NW, EW> {
    pub fn new() -> Self {
        Self {
            nodes: Vector::new(),
            edges: Vector::new(),
            /// unused_node and unused_edges themselves uses the Id pointer fields to construct a
            /// singly linked list to recycle items that are removed from previous operations.
            /// Removing nodes or edges work alike, by prepending themselves to the beginning of
            /// the list.
            unused_node: INVALID,
            unused_edge: INVALID,
        }
    }

    fn node(&self, ni: NodeId) -> Option<&Node<NW>> {
        let maybe_ret_node = self.nodes.get(ni.0 as usize);
        match maybe_ret_node {
            Some(Node {
                weight: Some(_),
                edges: _,
            }) => maybe_ret_node,
            _ => None,
        }
    }

    fn edge(&self, ei: EdgeId) -> Option<&Edge<EW>> {
        let maybe_ret_edge = self.edges.get(ei.0 as usize);
        match maybe_ret_edge {
            Some(Edge {
                weight: Some(_),
                from: _,
                to: _,
                next: _,
                prev: _,
            }) => maybe_ret_edge,
            _ => None,
        }
    }

    pub fn node_weight(&self, ni: NodeId) -> Option<&NW> {
        self.node(ni).map(|n| n.weight())
    }

    pub fn edge_weight(&self, ei: EdgeId) -> Option<&EW> {
        self.edge(ei).map(|e| e.weight())
    }

    pub fn edge_endpoints(&self, ei: EdgeId) -> Option<(NodeId, NodeId)> {
        self.edge(ei).map(|e| (e.from, e.to))
    }

    /// Creating a new node in the graph.
    pub fn add_node(&mut self, weight: NW) -> NodeId {
        let mut new_node = Node::new(weight);
        if self.unused_node != INVALID {
            let ret = self.unused_node;
            let node_mut = self.nodes.get_mut(ret as usize).unwrap();
            self.unused_node = node_mut.edges[OUTGOING];
            std::mem::swap(&mut new_node, node_mut);
            NodeId(ret)
        } else {
            let ret: IdType = self.nodes.len().try_into().expect("NodeId overflow");
            self.nodes.push_back(new_node);
            NodeId(ret)
        }
    }

    pub fn add_edge(&mut self, from: NodeId, to: NodeId, weight: EW) -> EdgeId {
        let mut new_edge = Edge::new(weight, from, to);
        let from_idx = from.0 as usize;
        let to_idx = to.0 as usize;

        let ret = if self.unused_edge != INVALID {
            let edge_id = self.unused_edge;
            let edges_mut = self.edges.get_mut(edge_id as usize).unwrap();
            self.unused_edge = edges_mut.next[OUTGOING];
            edge_id
        } else {
            let edge_id: IdType = self.edges.len().try_into().expect("EdgeId overflow");
            edge_id
        };
        // Prepend new edge into the edge lists
        let from_node_out_edge_list = &mut self.nodes[from_idx].edges[OUTGOING];
        new_edge.next[OUTGOING] = *from_node_out_edge_list;
        *from_node_out_edge_list = ret;

        let to_node_in_edge_list = &mut self.nodes[to_idx].edges[INCOMING];
        new_edge.next[INCOMING] = *to_node_in_edge_list;
        *to_node_in_edge_list = ret;

        // New edge default prev is INVALID, which is ok. Patch the next nodes in both doubly
        // linked lists and make new_edge->next->prev == new_edge
        for dir in [OUTGOING, INCOMING] {
            let next_idx = new_edge.next[dir] as usize;
            if let Some(next_edge) = self.edges.get_mut(next_idx) {
                next_edge.prev[dir] = ret;
            }
        }

        if ret as usize == self.edges.len() {
            self.edges.push_back(new_edge);
        } else {
            assert!((ret as usize) < self.edges.len());
            std::mem::swap(&mut new_edge, self.edges.get_mut(ret as usize).unwrap());
        }
        EdgeId(ret)
    }

    // TODO: Introduce edges iterator
    pub fn edges_directed(&self, ni: NodeId, dir: Direction) -> Vec<EdgeId> {
        let mut ret = Vec::new();
        let mut ei = self.nodes[ni.0 as usize].edges[dir as usize];
        while ei != INVALID {
            ret.push(EdgeId(ei));
            ei = self.edges[ei as usize].next[dir as usize];
        }
        ret
    }

    fn node_exists(&self, ni: NodeId) -> bool {
        let Some(node) = self.nodes.get(ni.0 as usize) else {
            return false;
        };
        node.weight.is_some()
    }

    fn edge_exists(&self, ei: EdgeId) -> bool {
        let Some(edge) = self.edges.get(ei.0 as usize) else {
            return false;
        };
        edge.weight.is_some()
    }

    /// Removes the node along with all edges that associated with it.
    pub fn remove_node(&mut self, ni: NodeId) -> Option<NW> {
        if !self.node_exists(ni) {
            return None;
        }
        // First remove all edges associated with the node.
        let out_edges = self.edges_directed(ni, Direction::Outgoing).into_iter();
        let in_edges = self.edges_directed(ni, Direction::Incoming).into_iter();
        out_edges.chain(in_edges).for_each(|ei| {
            self.remove_edge(ei);
        });

        let mut ret = None;
        let old_node = &mut self.nodes[ni.0 as usize];
        std::mem::swap(&mut ret, &mut old_node.weight);
        old_node.edges = [INVALID, INVALID];
        old_node.edges[OUTGOING] = self.unused_node;
        self.unused_node = ni.0;
        ret
    }

    /// Removes the edge.
    pub fn remove_edge(&mut self, ei: EdgeId) -> Option<EW> {
        if !self.edge_exists(ei) {
            return None;
        }

        let edge_idx = ei.0;
        let Some(edge_rep) = self.edges.get_mut(edge_idx as usize) else {
            return None;
        };

        let mut replacement_edge = Edge {
            weight: None,
            from: NodeId(INVALID),
            to: NodeId(INVALID),
            next: [INVALID, INVALID],
            prev: [INVALID, INVALID],
        };

        replacement_edge.next[OUTGOING] = self.unused_edge;
        self.unused_edge = edge_idx;
        std::mem::swap(edge_rep, &mut replacement_edge);
        let old_edge = replacement_edge;

        // Disconnect the edge from the linked lists
        for dir in [OUTGOING, INCOMING] {
            let next_edge_idx = old_edge.next[dir];
            let prev_edge_idx = old_edge.prev[dir];

            if let Some(next_edge) = self.edges.get_mut(next_edge_idx as usize) {
                next_edge.prev[dir] = prev_edge_idx;
            }

            if let Some(prev_edge) = self.edges.get_mut(prev_edge_idx as usize) {
                prev_edge.next[dir] = next_edge_idx;
            }
        }

        old_edge.weight
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn test_basic_insertion() {
        let mut graph = ImmutableGraph::new();
        let node5 = graph.add_node(5);
        let node6 = graph.add_node(6);
        let edge1 = graph.add_edge(node5, node6, 1);
        let edge2 = graph.add_edge(node5, node6, 2);
        assert_eq!(
            vec![edge2, edge1],
            graph.edges_directed(node5, Direction::Outgoing)
        );
        assert_eq!(
            Vec::<EdgeId>::from_iter([]),
            graph.edges_directed(node5, Direction::Incoming)
        );
        assert_eq!(
            vec![edge2, edge1],
            graph.edges_directed(node6, Direction::Incoming)
        );
        assert_eq!(
            Vec::<EdgeId>::from_iter([]),
            graph.edges_directed(node6, Direction::Outgoing)
        );

        graph.remove_node(node5);
        let new_node15 = graph.add_node(15);
        assert_eq!(node5, new_node15);
        assert_eq!(graph.node_weight(new_node15).unwrap(), &15);

        let node7 = graph.add_node(7);
        assert_eq!(node7, NodeId(2));
    }
}
