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
	
	protected boolean checkCloseMetamodellingRule() {
		for (Node node1 : this.m_tableau.metamodellingNodes) {
			for (Node node2 : this.m_tableau.metamodellingNodes) {
				if (this.m_tableau.m_metamodellingManager.checkCloseMetamodellingRuleIteration(node1, node2)) return true;
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
	
	protected boolean checkCloseMetaRule() {
		for (Node node0 : this.m_tableau.metamodellingNodes) {
    		for (Node node1 : this.m_tableau.metamodellingNodes) {
    			Node node0Eq = node0.getCanonicalNode();
    			Node node1Eq = node1.getCanonicalNode();    
    			for (OWLMetaRuleAxiom mrAxiom : this.m_tableau.m_permanentDLOntology.getMetaRuleAxioms()) {
        			String propertyRString = mrAxiom.getPropertyR().toString();		
        			if (!this.m_tableau.nodeRelations.containsKey(node0Eq.m_nodeID) || (this.m_tableau.nodeRelations.containsKey(node0Eq.m_nodeID) && this.m_tableau.nodeRelations.get(node0Eq.m_nodeID).containsKey(propertyRString) && !this.m_tableau.nodeRelations.get(node0Eq.m_nodeID).get(propertyRString).contains(node1Eq.m_nodeID))) {
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
		}
		return false;
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
    			// get property <#R> of MetaRule (<#R> <#S>)
    			String metaRulePropertyR = mrAxiom.getPropertyR().toString();
    			// get nodes [b1,b2, ... ,bn] / R(a,b1), R(a,b2), ... , R(a,bn) and bi = m Bi 
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
	
	// retorna el metamodellingNode asociado al individuo pasado por parametro e.
    public Node getMetamodellingNodeFromIndividual(OWLIndividual individual) {
    	return this.m_tableau.mapNodeIdtoNodes.get(this.m_tableau.metaIndividualToNodeID.get(individual.toString()));
    }
    
    // dado [b1,b2 ... ,bn] retorna [B1,B2, ... ,BN] / b1 = m B1, b2 = m B2, ... , bn = m Bn
    private List<String> getNodesClasses(List<Node> nodes) {
    	List<String> classes = new ArrayList<String>();
    	for (Node node : nodes) {
    		classes.addAll(this.m_tableau.classOfMetamodellingAxiom.get(node.m_nodeID));
    	}
    	return classes;
    }
	
	protected boolean checkPropertyNegationNew() {
    	boolean findClash = false;
    	if (this.m_tableau.m_unrelatedNodes.isEmpty()) {
    		return findClash;
    	}
    	else {
    		for (Node node0 : this.m_tableau.metamodellingNodes) {
        		for (Node node1 : this.m_tableau.metamodellingNodes) {
        			// R1(), R2(), ... , Rn() -> 
        			List<String> propertiesRForEqNodes = getRelationsOfNodes(node0, node1);
        			for (String propertyR : propertiesRForEqNodes) {
        				if (areUnrelatedNodes(node0,node1,getNegativeProperty(propertyR))) {
    						DependencySet clashDependencySet = this.m_tableau.m_dependencySetFactory.getActualDependencySet();
    						this.m_tableau.m_extensionManager.setClash(clashDependencySet);
    						findClash = true;
    						break;
        				}
        			}
        		}
        	}
        	return findClash;
    	}
	}
	
	private List<String> getRelationsOfNodes(Node node0, Node node1) {
		Set<String> relations = new HashSet<String>();
		if (this.m_tableau.nodeRelations.containsKey(node0.m_nodeID)) {
			for(Map.Entry<String,List<Integer>> entry : this.m_tableau.nodeRelations.get(node0.m_nodeID).entrySet()) {
				String property = entry.getKey();
				// aR -> l, esa l contiene a b o b_canonico.
				if (this.m_tableau.nodeRelations.get(node0.m_nodeID).get(property).contains(node1.m_nodeID) || this.m_tableau.nodeRelations.get(node0.m_nodeID).get(property).contains(node1.getCanonicalNode().m_nodeID)) {
					relations.add(property);
    			}
    		}
    	}
    	if (this.m_tableau.nodeRelations.containsKey(node0.getCanonicalNode().m_nodeID)) {
    		for(Map.Entry<String,List<Integer>> entry : this.m_tableau.nodeRelations.get(node0.getCanonicalNode().m_nodeID).entrySet()) {
				String property = entry.getKey();
				// aR -> l, esa l contiene a b o b_canonico.
				if (this.m_tableau.nodeRelations.get(node0.getCanonicalNode().m_nodeID).get(property).contains(node1.m_nodeID) || this.m_tableau.nodeRelations.get(node0.getCanonicalNode().m_nodeID).get(property).contains(node1.getCanonicalNode().m_nodeID)) {
					relations.add(property);
    			}
    		}
    	}
		return new ArrayList<String>(relations);
	}
	
	private boolean areUnrelatedNodes(Node node0, Node node1, String property) {
		if (this.m_tableau.m_unrelatedNodes.containsKey(node0.m_nodeID) && this.m_tableau.m_unrelatedNodes.get(node0.m_nodeID).containsKey(property)) {
			// a~R -> l, esa l contiene a b o b_canonico.
			if (this.m_tableau.m_unrelatedNodes.get(node0.m_nodeID).get(property).contains(node1.m_nodeID) || this.m_tableau.m_unrelatedNodes.get(node0.m_nodeID).get(property).contains(node1.getCanonicalNode().m_nodeID)) {
				return true;
			}
    	}
    	if (this.m_tableau.m_unrelatedNodes.containsKey(node0.getCanonicalNode().m_nodeID) && this.m_tableau.m_unrelatedNodes.get(node0.getCanonicalNode().m_nodeID).containsKey(property)) {
			// aR -> l, esa l contiene a b o b_canonico.
			if (this.m_tableau.m_unrelatedNodes.get(node0.getCanonicalNode().m_nodeID).get(property).contains(node1.m_nodeID) || this.m_tableau.m_unrelatedNodes.get(node0.getCanonicalNode().m_nodeID).get(property).contains(node1.getCanonicalNode().m_nodeID)) {
				return true;
			}    		
    	}
		return false;
	}
    
    private String getNegativeProperty(String property) {
    	String prefix = "<~";
    	String negativeProperty = prefix + property.substring(1);
    	return negativeProperty;
    }
  
}
