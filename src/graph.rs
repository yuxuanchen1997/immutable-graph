// Copyright (c) 2023 Yuxuan Chen

use im::Vector;

/// DiGraph implemented with immutable vector (RRB).

#[derive(Copy, Clone)]
pub enum Direction {
    Outgoing = 0,
    Incoming = 1,
}

const OUTGOING: usize = Direction::Outgoing as usize;
const INCOMING: usize = Direction::Incoming as usize;

pub type IdType = u8;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct NodeId(IdType);
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct EdgeId(IdType);

// Sentinel to end linked lists.
const INVALID: IdType = IdType::MAX;

/// Representation of a Node or a vacant spot if it's found as a part of unused_nodes. When a node
/// is present, the edges array stores pointers to heads of two linked lists.
#[derive(Clone)]
pub struct Node {
    weight: Option<i32>,
    edges: [IdType; 2],
}

impl Node {
    pub fn new(weight: i32) -> Self {
        Self {
            weight: Some(weight),
            edges: [INVALID, INVALID]
        }
    }

    pub fn weight(&self) -> i32 {
        self.weight.unwrap()
    }
}

/// Because edges are accessible from both ends, each edge is considered an element of two linked
/// lists. One originated from each direction. 
#[derive(Clone)]
pub struct Edge {
    weight: Option<i32>,
    from: NodeId,
    to: NodeId,
    /// next[OUTGOING] is next in the chain when the edge is a part of a successor list.
    /// next[INCOMING] is next in the chain when the edge is a part of a predecessor list.
    next: [IdType; 2],
}

impl Edge {
    pub fn new(weight: i32, from: NodeId, to: NodeId) -> Self {
        Self {
            weight: Some(weight), 
            from,
            to,
            next: [INVALID, INVALID]
        }
    }

    pub fn weight(&self) -> i32 {
        self.weight.unwrap()
    }
}

/// Contraray to its name, `ImmutableGraph` has mutable semantics. The immutable bits of it are the
/// underlying data structure that backs the storage of the nodes and edges, which makes it trivial
/// to copy. This is useful in many cases: e.g. A graph building process that requires bookkeeping
/// intermediate steps, or algorithms that requires back tracking. `NodeId`s and `EdgeId`s of this
/// graph is stable for each `ImmutableGraph` object and cloned copies. (i.e. The indices into the 
/// rest of the graph do not change when nodes and edges are removed from the graph.)
#[derive(Clone, Default)]
pub struct ImmutableGraph {
    /// By using im::Vector, the internal structure of this immutable graph is O(1) copy.
    nodes: Vector<Node>,
    edges: Vector<Edge>,
    unused_node: IdType,
    unused_edge: IdType,
}

impl ImmutableGraph {
    pub fn new() -> Self {
        Self {
            /// unused_node and unused_edges themselves uses the Id pointer fields to construct a
            /// singly linked list to recycle items that are removed from previous operations.
            /// Removing nodes or edges work alike, by prepending themselves to the beginning of
            /// the list. 
            unused_node: INVALID,
            unused_edge: INVALID,
            ..Default::default() 
        }
    }

    pub fn node(&self, ni: NodeId) -> Option<&Node> {
        let maybe_ret_node = self.nodes.get(ni.0 as usize);
        match maybe_ret_node {
            Some(Node {weight: Some(_), edges: _}) => maybe_ret_node,
            _ => None,
        }
    }

    pub fn edge(&self, ei: EdgeId) -> Option<&Edge> {
        let maybe_ret_edge = self.edges.get(ei.0 as usize);
        match maybe_ret_edge {
            Some(Edge {weight: Some(_), from: _, to: _, next: _}) => maybe_ret_edge,
            _ => None,
        }
    }
    
    pub fn node_weight(&self, ni: NodeId) -> Option<i32> {
        self.node(ni).map(|n| n.weight())
    }

    pub fn edge_weight(&self, ei: EdgeId) -> Option<i32> {
        self.edge(ei).map(|e| e.weight())
    }

    pub fn edge_endpoints(&self, ei: EdgeId) -> Option<(NodeId, NodeId)> {
        self.edge(ei).map(|e| (e.from, e.to))
    }

    /// Creating a new node in the graph. 
    pub fn add_node(&mut self, weight: i32) -> NodeId {
        // TODO: use unused_nodes. 
        let ret: IdType = self.nodes.len().try_into().expect("NodeId overflow");
        self.nodes.push_back(Node::new(weight));
        NodeId(ret)
    }

    pub fn add_edge(&mut self, from: NodeId, to: NodeId, weight: i32) -> EdgeId {
        // TODO: use unused_edges.
        let ret: IdType = self.edges.len().try_into().expect("EdgeId overflow");
        let mut new_edge = Edge::new(weight, from, to);
        let from_idx = from.0 as usize;
        let to_idx = to.0 as usize;
        new_edge.next[OUTGOING] = self.nodes[from_idx].edges[OUTGOING];
        self.nodes[from_idx].edges[OUTGOING] = ret;
        new_edge.next[INCOMING] = self.nodes[to_idx].edges[INCOMING];
        self.nodes[to_idx].edges[INCOMING] = ret;
        self.edges.push_back(new_edge);
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

    pub fn remove_node(&mut self, ni: NodeId) -> Option<i32> {
        todo!()
    }

    pub fn remove_edge(&mut self, ei: EdgeId) -> Option<i32> {
        todo!()
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
        assert_eq!(vec![edge2, edge1], graph.edges_directed(node5, Direction::Outgoing));
        assert_eq!(Vec::<EdgeId>::from_iter([]), graph.edges_directed(node5, Direction::Incoming));
        assert_eq!(vec![edge2, edge1], graph.edges_directed(node6, Direction::Incoming));
        assert_eq!(Vec::<EdgeId>::from_iter([]), graph.edges_directed(node6, Direction::Outgoing));
    }
}
