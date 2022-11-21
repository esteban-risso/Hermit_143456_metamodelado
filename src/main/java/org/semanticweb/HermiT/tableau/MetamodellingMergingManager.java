package org.semanticweb.HermiT.tableau;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public final class MetamodellingMergingManager {
	
	protected final Object[] m_binaryAuxiliaryTuple;
	protected Map<Integer, Integer> m_mergeInto;
    protected Map<Integer, Set<Integer>> m_canonicalNodeOf;
	protected Map<Integer, Integer> m_previousMergeInto;
    protected Map<Integer, Set<Integer>> m_previousCanonicalNodeOf;
    protected Object[] m_previousMetamodellingMergingManager;
    protected Object[] m_actualMetamodellingMergingManager;


    public MetamodellingMergingManager() {
    	this.m_binaryAuxiliaryTuple = new Object[2];
    }

    public void clear() {
    	this.m_mergeInto.clear();
    	this.m_canonicalNodeOf.clear();
    }

    public void mergeNodes(Node node, Node mergeInto) {
    	if (this.m_actualMetamodellingMergingManager != null ) {
    		//this.m_previousMetamodellingMergingManager[0]
    	}
    	if (this.m_canonicalNodeOf.containsKey(node.m_nodeID)) {
    		Set<Integer> canonicalNodeOf = this.m_canonicalNodeOf.get(node.m_nodeID);
        	if (!canonicalNodeOf.isEmpty()) {
        		for (Integer node_id: canonicalNodeOf) {
        			this.m_mergeInto.put(node_id, mergeInto.m_nodeID);
        		}
        		this.m_canonicalNodeOf.putIfAbsent(mergeInto.m_nodeID, new HashSet<Integer>());
        		this.m_canonicalNodeOf.get(mergeInto.m_nodeID).addAll(canonicalNodeOf);
            	this.m_canonicalNodeOf.get(node.m_nodeID).clear();
        	}
    	}
    	this.m_canonicalNodeOf.putIfAbsent(mergeInto.m_nodeID, new HashSet<Integer>());
    	this.m_canonicalNodeOf.get(mergeInto.m_nodeID).add(node.m_nodeID);
    	this.m_mergeInto.put(node.m_nodeID, mergeInto.m_nodeID);
    	this.m_binaryAuxiliaryTuple[0] = node;
    	this.m_binaryAuxiliaryTuple[1] = mergeInto;	
    }

}

