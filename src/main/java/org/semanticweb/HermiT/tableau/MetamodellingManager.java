package org.semanticweb.HermiT.tableau;

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.semanticweb.HermiT.model.Atom;
import org.semanticweb.HermiT.model.AtomicRole;
import org.semanticweb.HermiT.model.DLPredicate;
import org.semanticweb.HermiT.model.Equality;
import org.semanticweb.HermiT.model.Individual;
import org.semanticweb.HermiT.model.Inequality;
import org.semanticweb.HermiT.model.Term;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLMetaRuleAxiom;
import org.semanticweb.owlapi.model.OWLMetamodellingAxiom;

public final class MetamodellingManager {
	
	protected final Tableau m_tableau;
	protected Map<OWLClassExpression,Map<OWLClassExpression,Atom>> inequalityMetamodellingPairs;
	protected List<String> defAssertions;
	
	public MetamodellingManager(Tableau tableau) {
		this.m_tableau = tableau;
		inequalityMetamodellingPairs = new HashMap<OWLClassExpression,Map<OWLClassExpression,Atom>>();
		defAssertions = new ArrayList<String>();
	}
	
	public boolean checkEqualMetamodellingRuleIteration(Node node0, Node node1) {
		// node0 = m A1, node0 = m A2, ... , node0 = m An -> [A1,A2, ... ,An]
		List<OWLClassExpression> node0Classes = MetamodellingAxiomHelper.getMetamodellingClassesByIndividual(this.m_tableau.getNodeToMetaIndividual().get(node0.getNodeID()), this.m_tableau.getPermanentDLOntology());
		// node1 = m B1, node0 = m B2, ... , node0 = m Bn -> [B1,B2, ... ,Bn]
		List<OWLClassExpression> node1Classes = MetamodellingAxiomHelper.getMetamodellingClassesByIndividual(this.m_tableau.getNodeToMetaIndividual().get(node1.getNodeID()), this.m_tableau.getPermanentDLOntology());
		if (!node0Classes.isEmpty() && !node1Classes.isEmpty()) {	
			for (OWLClassExpression node0Class : node0Classes) {
				for (OWLClassExpression node1Class : node1Classes) {
					// check if <#A>(X) :- <#B>(X), <#B>(X) :- <#A>(X) are not in m_dlClauses
					if (node1Class != node0Class && (!MetamodellingAxiomHelper.containsSubClassOfAxiom( node0Class, node1Class, this.m_tableau.getPermanentDLOntology()) || !MetamodellingAxiomHelper.containsSubClassOfAxiom(node1Class, node0Class, this.m_tableau.getPermanentDLOntology()))) {
						// add <#A>(X) :- <#B>(X), <#B>(X) :- <#A>(X) in m_dlClauses
						MetamodellingAxiomHelper.addSubClassOfAxioms(node0Class, node1Class, this.m_tableau.getPermanentDLOntology(), this.m_tableau);
						return true;
					}
				}
			}
		}
		return false;
	}
	
	public boolean checkInequalityMetamodellingRuleIteration(Node node0, Node node1) {
		List<OWLClassExpression> node0Classes = MetamodellingAxiomHelper.getMetamodellingClassesByIndividual(this.m_tableau.getNodeToMetaIndividual().get(node0.getNodeID()), this.m_tableau.getPermanentDLOntology());
		List<OWLClassExpression> node1Classes = MetamodellingAxiomHelper.getMetamodellingClassesByIndividual(this.m_tableau.getNodeToMetaIndividual().get(node1.getNodeID()), this.m_tableau.getPermanentDLOntology());
		if (!node0Classes.isEmpty() && !node1Classes.isEmpty()) {
			for (OWLClassExpression node0Class : node0Classes) {
				for (OWLClassExpression node1Class : node1Classes) {					
					if (node1Class != node0Class) { 
						Atom def0 = null;
						if (this.inequalityMetamodellingPairs.containsKey(node1Class) && this.inequalityMetamodellingPairs.get(node1Class).containsKey(node0Class)) {
							def0 = this.inequalityMetamodellingPairs.get(node1Class).get(node0Class);
						}
						if (this.inequalityMetamodellingPairs.containsKey(node0Class) && this.inequalityMetamodellingPairs.get(node0Class).containsKey(node1Class)) {
							def0 = this.inequalityMetamodellingPairs.get(node0Class).get(node1Class);
						}
						if (def0 == null || (def0 != null && !this.m_tableau.containsClassAssertion(def0.getDLPredicate().toString()))) {
							MetamodellingAxiomHelper.addInequalityMetamodellingRuleAxiom(node0Class, node1Class, this.m_tableau.getPermanentDLOntology(), this.m_tableau, def0, this.inequalityMetamodellingPairs);
							return true;
						}
					}
				}
			}
		}
		return false;
	}
	
	public boolean checkCloseMetamodellingRuleIteration(Node node0, Node node1) {
		Node node0Equivalent = node0.getCanonicalNode();
		Node node1Equivalent = node1.getCanonicalNode();
		if (!this.m_tableau.areDifferentIndividual(node0Equivalent, node1Equivalent) && !this.m_tableau.areSameIndividual(node0Equivalent, node1Equivalent) && !this.m_tableau.alreadyCreateDisjunction(node0Equivalent, node1Equivalent)) {
			
			// <#node0Equivalent> == <#node1Equivalent>
			Atom eqAtom = Atom.create(Equality.INSTANCE, this.m_tableau.getMapNodeIndividual().get(node0Equivalent.getNodeID()), this.m_tableau.getMapNodeIndividual().get(node1Equivalent.getNodeID()));
			// ==
			DLPredicate equalityPredicate = eqAtom.getDLPredicate();
			// <#node0Equivalent> != <#node1Equivalent>
			Atom ineqAtom = Atom.create(Inequality.INSTANCE, this.m_tableau.getMapNodeIndividual().get(node0Equivalent.getNodeID()), this.m_tableau.getMapNodeIndividual().get(node1Equivalent.getNodeID()));
			// !=
			DLPredicate inequalityPredicate = ineqAtom.getDLPredicate();
			// [==,!=]
			DLPredicate[] dlPredicates = new DLPredicate[] {equalityPredicate, inequalityPredicate};			
			int hashCode = 0;
            for (int disjunctIndex = 0; disjunctIndex < dlPredicates.length; ++disjunctIndex) {
                hashCode = hashCode * 7 + dlPredicates[disjunctIndex].hashCode();
            }
            // == (0) \/ != (0)
            GroundDisjunctionHeader gdh = new GroundDisjunctionHeader(dlPredicates, hashCode , null);
			DependencySet dependencySet = this.m_tableau.m_dependencySetFactory.getActualDependencySet();
			// node0Equivalent == node1Equivalent v !=(node0Equivalent,node1Equivalent)
			GroundDisjunction groundDisjunction = new GroundDisjunction(this.m_tableau, gdh, new Node[] {node0Equivalent, node1Equivalent, node0Equivalent, node1Equivalent}, new boolean[] {true, true}, dependencySet);
			if (!this.m_tableau.alreadyCreateDisjunction(node0Equivalent, node1Equivalent) && !groundDisjunction.isSatisfied(this.m_tableau)) {
				this.m_tableau.addGroundDisjunction(groundDisjunction);
				this.m_tableau.addCreatedDisjuntcion(node0Equivalent, node1Equivalent);
				return true;
			}
		}
		return false;
	}
	
	protected boolean checkPropertyNegation() {
    	boolean findClash = false;
    	for (Node node0 : this.m_tableau.metamodellingNodes) {
    		for (Node node1 : this.m_tableau.metamodellingNodes) {
    			List<String> propertiesRForEqNodes = getObjectProperties(node0, node1);
    			for (String propertyR : propertiesRForEqNodes) {
    				for (String propertyIter : propertiesRForEqNodes) {
    					if (propertyIter.equals("<~"+propertyR.substring(1))) {
    						DependencySet clashDependencySet = this.m_tableau.m_dependencySetFactory.getActualDependencySet();
    						this.m_tableau.m_extensionManager.setClash(clashDependencySet);
    						findClash = true;
    						break;
    					}
    				}
    			}
    		}
    	}
    	return findClash;
    }
	
	protected boolean checkCloseMetaRule() {
		for (Node node0 : this.m_tableau.metamodellingNodes) {
    		for (Node node1 : this.m_tableau.metamodellingNodes) {
    			Node node0Eq = node0.getCanonicalNode();
    			Node node1Eq = node1.getCanonicalNode();
    			// R1(node0Eq,node1Eq), ... , Rn(node0Eq,node1Eq) -> list = [R1, ... ,Rn]
    			List<String> propertiesRForEqNodes = getObjectProperties(node0Eq, node1Eq);
				// R / MetaRule(R,S) and R not in list
    			String propertyRString = meetCloseMetaRuleCondition(propertiesRForEqNodes);
    			if (!propertyRString.equals("")) {
    				if (!isCloseMetaRuleDisjunctionAdded(propertyRString, node0Eq, node1Eq)) {
    					// <#R> v <~#R>
    					GroundDisjunction groundDisjunction = createCloseMetaRuleDisjunction(propertyRString, node0Eq, node1Eq);
	    				if (!groundDisjunction.isSatisfied(this.m_tableau)) {
    						this.m_tableau.addGroundDisjunction(groundDisjunction);
    							return true;
    					}
    				}		
    			}
    		}
    	}
    	return false;
    }
	
	private List<String> getObjectProperties(Node node0, Node node1) {
    	Set<String> objectProperties = new HashSet<String>();
    	if (this.m_tableau.nodeProperties.containsKey(node0.getCanonicalNode().m_nodeID)) {
    		if (this.m_tableau.nodeProperties.get(node0.getCanonicalNode().m_nodeID).containsKey(node1.getCanonicalNode().m_nodeID)) {
    			objectProperties.addAll(this.m_tableau.nodeProperties.get(node0.getCanonicalNode().m_nodeID).get(node1.getCanonicalNode().m_nodeID));
    		}
    	}
    	if (this.m_tableau.nodeProperties.containsKey(node0.getCanonicalNode().m_nodeID)) {
    		if (this.m_tableau.nodeProperties.get(node0.getCanonicalNode().m_nodeID).containsKey(node1.m_nodeID)) {
    			objectProperties.addAll(this.m_tableau.nodeProperties.get(node0.getCanonicalNode().m_nodeID).get(node1.m_nodeID));
    		}
    	}
    	if (this.m_tableau.nodeProperties.containsKey(node0.m_nodeID)) {
    		if (this.m_tableau.nodeProperties.get(node0.m_nodeID).containsKey(node1.getCanonicalNode().m_nodeID)) {
    			objectProperties.addAll(this.m_tableau.nodeProperties.get(node0.m_nodeID).get(node1.getCanonicalNode().m_nodeID));
    		}
    	}
    	if (this.m_tableau.nodeProperties.containsKey(node0.m_nodeID)) {
    		if (this.m_tableau.nodeProperties.get(node0.m_nodeID).containsKey(node1.m_nodeID)) {
    			objectProperties.addAll(this.m_tableau.nodeProperties.get(node0.m_nodeID).get(node1.m_nodeID));
    		}
    	}
    	return new ArrayList<String>(objectProperties);
    }
	
	// chequea si la disjuncion esta o no.
	private boolean isCloseMetaRuleDisjunctionAdded(String propertyRString, Node node0, Node node1) {
		// mapa de disjunciones.
		if (this.m_tableau.closeMetaRuleDisjunctionsMap.containsKey(propertyRString)) {
    		for (Map.Entry<Node, Node> nodePair : this.m_tableau.closeMetaRuleDisjunctionsMap.get(propertyRString)) {
    			if (nodePair.getKey().m_nodeID == node0.m_nodeID && nodePair.getValue().m_nodeID == node1.m_nodeID) {
    				return true;
    			}
    		}
    	} else {
    		this.m_tableau.closeMetaRuleDisjunctionsMap.put(propertyRString, new ArrayList<Map.Entry<Node, Node>>());
    	}
    	this.m_tableau.closeMetaRuleDisjunctionsMap.get(propertyRString).add(new AbstractMap.SimpleEntry<>(node0, node1));
    	return false;
    }
    
    private GroundDisjunction createCloseMetaRuleDisjunction(String propertyRString, Node node0Eq, Node node1Eq) {
    	// R
    	propertyRString = propertyRString.substring(1, propertyRString.length()-1);
		// <~#R>
    	AtomicRole newProperty = AtomicRole.create("~"+propertyRString);
    	// <#R>
    	AtomicRole propertyR = AtomicRole.create(propertyRString);    				
		// <#R> (node0Eq,node1Eq)
    	Atom relationR = Atom.create(propertyR, (Term)this.m_tableau.mapNodeIndividual.get(node0Eq.m_nodeID), (Term)this.m_tableau.mapNodeIndividual.get(node1Eq.m_nodeID));	
		// #R
    	DLPredicate relationRPredicate = relationR.getDLPredicate();
		// <~#R> (node0Eq,node1Eq)
    	Atom newRelationR = Atom.create(newProperty, (Term)this.m_tableau.mapNodeIndividual.get(node0Eq.m_nodeID), (Term)this.m_tableau.mapNodeIndividual.get(node1Eq.m_nodeID));	
		// ~#R
    	DLPredicate newRelationRPredicate = newRelationR.getDLPredicate();
		// [#R,~#R]
    	DLPredicate[] dlPredicates = new DLPredicate[] {relationRPredicate, newRelationRPredicate};
		int hashCode = 0;
        for (int disjunctIndex = 0; disjunctIndex < dlPredicates.length; ++disjunctIndex) {
            hashCode = hashCode * 7 + dlPredicates[disjunctIndex].hashCode();
        }    	            
        // #R (0) \/ ~#R (0)
        GroundDisjunctionHeader gdh = new GroundDisjunctionHeader(dlPredicates, hashCode , null);
		DependencySet dependencySet = this.m_tableau.m_dependencySetFactory.getActualDependencySet();
		// <#R> (node0Eq,node1Eq) v <~#R> (node0Eq,node1Eq)
		GroundDisjunction groundDisjunction = new GroundDisjunction(this.m_tableau, gdh, new Node[] {node0Eq, node1Eq, node0Eq, node1Eq}, new boolean[] {true, true}, dependencySet);
		return groundDisjunction;
    }
    
    protected boolean checkMetaRule() {
    	// iteration over axioms Metamodelling(<#a> <#A>)
    	for (OWLMetamodellingAxiom metamodellingAxiom : this.m_tableau.m_permanentDLOntology.getMetamodellingAxioms()) {
    		// return the metamodelling node associated with the individual <#a> / Metamodelling(<#a> <#A>)
    		Node metamodellingNode = getMetamodellingNodeFromIndividual(metamodellingAxiom.getMetamodelIndividual());
    		// iteration over axioms MetaRule (<#R> <#S>)
    		for (OWLMetaRuleAxiom mrAxiom : this.m_tableau.m_permanentDLOntology.getMetaRuleAxioms()) {
    			// <#R>
    			String metaRulePropertyR = mrAxiom.getPropertyR().toString();
    			// R(a,b1), R(a,b2), ... , R(a,bn) and bi = m Bi -> [b1,b2, ... ,bn] 
    			List<Node> relatedNodes = this.m_tableau.getRelatedNodes(metamodellingNode, metaRulePropertyR);
    			if (relatedNodes.size() > 0) {
    				// b1 = m B1, b2 = m B2, ... , bn = m Bn -> [B1,B2, ... ,Bn]
    				List<String> classesImageForMetamodellingNode = getNodesClasses(relatedNodes);
    				if (!classesImageForMetamodellingNode.isEmpty() && !MetamodellingAxiomHelper.containsMetaRuleAddedAxiom(metamodellingAxiom.getModelClass().toString(), mrAxiom.getPropertyS().toString(), classesImageForMetamodellingNode, this.m_tableau)) {
    					MetamodellingAxiomHelper.addMetaRuleAddedAxiom(metamodellingAxiom.getModelClass().toString(), mrAxiom.getPropertyS().toString(), classesImageForMetamodellingNode, this.m_tableau);
    					return true;
    				}
    			}
    		}
    	}
    	return false;
    }
    
    public Node getMetamodellingNodeFromIndividual(OWLIndividual individual) {
    	int nodeId = -1;
    	// recorre nodeToIndividual para encontrar el individuo pasado como parametro.
    	for (int metamodellingNodeId : this.m_tableau.nodeToMetaIndividual.keySet()) {
    		// nodeToMetaIndividual[metamodellingNodeId] == individual (<#a1>)
    		if (this.m_tableau.nodeToMetaIndividual.get(metamodellingNodeId).toString().equals(individual.toString())) {
    			nodeId = metamodellingNodeId;
    		}
    	}
    	for (Node metamodellingNode : this.m_tableau.metamodellingNodes) {
    		if (nodeId == metamodellingNode.m_nodeID) {
    			return metamodellingNode;
    		}
    	}
    	return null;
    }
    
    // dado [b1,b2 ... ,bn] retorna [B1,B2, ... ,BN] / b1 = m B1, b2 = m B2, ... , bn = m Bn
    private List<String> getNodesClasses(List<Node> nodes) {
    	List<String> classes = new ArrayList<String>();
    	for (Node node : nodes) {
    		int nodeId = node.m_nodeID;
    		if (this.m_tableau.nodeToMetaIndividual.containsKey(nodeId)) {
    			Individual individual = this.m_tableau.nodeToMetaIndividual.get(nodeId);
    			for (OWLMetamodellingAxiom metamodellingAxiom : this.m_tableau.m_permanentDLOntology.getMetamodellingAxioms()) {
    				if (metamodellingAxiom.getMetamodelIndividual().toString().equals(individual.toString())) {
    					classes.add(metamodellingAxiom.getModelClass().toString());
    				}
    			}
    		}
    	}
    	return classes;
    }
    
	// retorna la propiedad R de un axioma MetaRule(R,S)/ R y ~R no se encuntre en el conjunto
	// de propiedades pasados por parametro. Dicha propiedad va a ser usada para crear la disyuncion (R v ~R).
    private String meetCloseMetaRuleCondition(List<String> propertiesRForEqNodes) {
    	for (OWLMetaRuleAxiom mrAxiom : this.m_tableau.m_permanentDLOntology.getMetaRuleAxioms()) {
    		String metaRulePropertyR = mrAxiom.getPropertyR().toString();
    		if (!propertiesRForEqNodes.contains(metaRulePropertyR) && !propertiesRForEqNodes.contains(getNegativeProperty(metaRulePropertyR))) {
				return metaRulePropertyR;
			}
    	}
    	return "";
    }
    
    private String getNegativeProperty(String property) {
    	String prefix = "<~";
    	String negativeProperty = prefix + property.substring(1);
    	return negativeProperty;
    }

protected boolean checkEqualMetamodellingRule() {
	boolean ruleApplied = false;
	for (Node node1 : this.m_tableau.metamodellingNodes) {
		for (Node node2 : this.m_tableau.metamodellingNodes) {
			if (this.m_tableau.areSameIndividual(node1, node2)) {
				if (checkEqualMetamodellingRuleIteration(node1, node2)) ruleApplied = true;
			}
		}
	}
	return ruleApplied;
}

protected boolean checkInequalityMetamodellingRule() {
	boolean ruleApplied = false;
	for (Node node1 : this.m_tableau.metamodellingNodes) {
		for (Node node2 : this.m_tableau.metamodellingNodes) {
			if (this.m_tableau.areDifferentIndividual(node1, node2)) {
				if (checkInequalityMetamodellingRuleIteration(node1, node2)) ruleApplied = true;
			}
		}
	}
	return ruleApplied;
}

protected boolean checkCloseMetamodellingRule() {
	for (Node node1 : this.m_tableau.metamodellingNodes) {
		for (Node node2 : this.m_tableau.metamodellingNodes) {
			if (this.m_tableau.m_metamodellingManager.checkCloseMetamodellingRuleIteration(node1, node2)) return true;
		}
	}
	return false;
}
}
