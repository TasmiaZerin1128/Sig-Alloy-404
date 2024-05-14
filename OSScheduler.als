
sig PID {}

// define the chain

abstract sig Node {
	pid: one PID,
	nextNode: lone Node
}

// chains are of three type

sig ReadyNode, BlockedNode, FreeNode extends Node {}

// all chains have a head
sig headFreeNode, tailFreeNode in FreeNode {}
sig headBlockedNode, tailBlockedNode in BlockedNode {}
sig headReadyNode, tailReadyNode in ReadyNode {}


fact ChainRules {
	
	// in a chain, there can not be any repitition of same nodes
	all node: Node | node not in node.^nextNode

	// head can not be the next of any node
	no nextNode.( headFreeNode + headBlockedNode + headReadyNode )

	// all nodes except for the head will be the next node for one node
	all node: Node - ( headFreeNode + headBlockedNode + headReadyNode ) 
		| one nextNode.node

	// no node can be the next of two different nodes
	no node1, node2, node3: Node | (node1 = nextNode.node2) and 
		(node1 = nextNode.node3)

	// no two nodes can share same id
	no node: Node | node.pid = node.^nextNode.pid

	// all nodes except tails cant have their next as null
	no node: Node - ( tailFreeNode + tailBlockedNode + tailReadyNode ) | node.nextNode = none

}

fact TailsAreLastNodes {
	all node: (tailFreeNode + tailBlockedNode + tailReadyNode) | 
		node.nextNode = none
}

fact NoSharedIdBetweenChains {

	// same id can not be present in multiple chains
	FreeNode.pid & ReadyNode.pid = none
	ReadyNode.pid & BlockedNode.pid = none
	BlockedNode.pid & FreeNode.pid = none

}


pred PushIntoChain[node, chain: Node, tail: Node] {

	// pushing when there is no data in the chain
	
	chain = none implies {
		node.nextNode = none
		chain = node
	}

	// pushing at end when the chain has some element
	
	some chain implies {
		( node.pid not in chain.^nextNode.pid ) implies {
			tail.nextNode = node
		}
	}

}


