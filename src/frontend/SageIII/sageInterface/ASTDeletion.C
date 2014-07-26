#include "rose.h"
#include "wholeAST.h"
#include <iostream>
#include <cstdlib>
#include <vector>
#include <deque>
namespace SI = SageInterface;

//#define ASTDELETION_DEBUG_MINIMAL
//#define ASTDELETION_DEBUG
//#define ASTDELETION_MEMORY_VISITOR_DEBUG
//#define ASTDELETION_CLEANUP_DEBUG
//#define ASTDELETION_TYPE_REMOVAL_DEBUG

namespace ASTDeletionSupport {



/****	PRINT FUNCTIONS FOR DEBUGGING PURPOSES  ****/

//printNode: Displays information about a given node. Used for debugging purposes.
void printNode(SgNode* node) {
	printf("node: %s = %s\n", node->sage_class_name(), node->unparseToString().c_str());
}


//printNodeExt: Extended print node function. Displays more information than the regular printNode function.
//Used for debugging purposes.
void printNodeExt(SgNode* node) {
	Sg_File_Info* File = isSgNode(node)->get_file_info();
	if(File != NULL){
		printf("File: (%s, line:%d, column:%d) %s = %s\n", File->get_filenameString().c_str(),
		File->get_line(),
		File->get_col(),
		isSgNode(node)->sage_class_name(),
		isSgNode(node)->unparseToString().c_str());
	} else {
		printNode(node);
	}
}




/**** FINDING SYMBOLS ASSOCIATED WITH NODES ****/
/* One of the most important parts of AST deletion is to identify symbols that are associated with */
/* the nodes we want to delete, and to remove those symbols if and when they are no longer needed. */
/* The following functions handle the process of finding the symbol associated with a node, if it  */
/* exists. The first function to be called is getAssociatedSymbol, which may delegate the task     */
/* to helper functions, namely handleDeclaration and handleExpression.				   */

//handleDeclaration: Attempts to retrieve a symbol associated with an SgDeclarationStatement node, if it exists.
SgSymbol* handleDeclaration(SgDeclarationStatement* decl){
	ROSE_ASSERT(decl != NULL);
	if(!decl->hasAssociatedSymbol())
		return NULL;

	SgDeclarationStatement* decl_to_search = decl;

	//From the ROSE documentation for SgMemberFunctionDeclaration nodes (circa July 2014):
	//The scope can at times be that of the global scope, when this happens users should access the scope through 
	//get_firstNondefiningDeclaration(). This appears to be a bug internally.	
	if(isSgMemberFunctionDeclaration(decl) /*&& isSgGlobal(isSgMemberFunctionDeclaration(decl)->get_scope())*/  )
	{			
		SgMemberFunctionDeclaration* mfd = isSgMemberFunctionDeclaration(decl);
		decl_to_search = mfd->get_firstNondefiningDeclaration();
	}
	
	//From the ROSE documentation for SgMemberFunctionDeclaration nodes (circa July 2014):
	//This should not be a SgDeclaration (should be a regular SgStatement). [...]
	//This will be fixed in a later release.
	if(isSgAsmStmt(decl_to_search))
		return NULL;

	//Using statements claim to have associated symbols, but what they really mean is that they can have a member that can have an associated symbol.
	if(isSgUsingDeclarationStatement(decl_to_search) || isSgUsingDirectiveStatement(decl_to_search) || isSgTemplateInstantiationDirectiveStatement(decl_to_search))
		return NULL;

	ROSE_ASSERT(decl_to_search != NULL);
	if(decl_to_search->get_firstNondefiningDeclaration()==NULL ||  decl_to_search->get_firstNondefiningDeclaration()->get_firstNondefiningDeclaration() == NULL)
		return NULL;
	
	SgSymbol* symbol = decl_to_search->get_symbol_from_symbol_table();
	
	return symbol;
}


//handleRefExp: reference expressions (not to be confused with SgRefExp nodes, which are unrelated (and deprecated))
//share similar interfaces for looking up their associated symbols, but are not derived from a class that distinguishes
//them from other SgExpression nodes. This template function makes it easier to handle such expressions as if they were
//related in that way.
template<typename RefExp>
SgSymbol* handleRefExp(RefExp* e){
	return  e->get_symbol();
}


//handleExpression: Attempts to retrieve a symbol associated with an SgExpression node, if it exists.
SgSymbol* handleExpression(SgExpression* expr){

	//reference expressions
	if(isSgVarRefExp(expr)) return handleRefExp((SgVarRefExp*) expr);
	if(isSgFunctionRefExp(expr)) return handleRefExp((SgFunctionRefExp*) expr);
	if(isSgMemberFunctionRefExp(expr)) return handleRefExp((SgMemberFunctionRefExp*) expr);
	if(isSgLabelRefExp(expr)) return handleRefExp((SgLabelRefExp*) expr);
	if(isSgClassNameRefExp(expr)) return handleRefExp((SgClassNameRefExp*) expr);

	//etc.
	if(isSgThisExp(expr)) return isSgThisExp(expr)->get_class_symbol();
	if(isSgUserDefinedBinaryOp(expr)) return isSgUserDefinedBinaryOp(expr)->get_symbol(); 

	return NULL;

}


//getAssociatedSymbol: Returns the symbol associated with this node, if one exists.
//Otherwise, this function will return NULL.
SgSymbol* getAssociatedSymbol(SgNode* node){
	
	//Initialized names.
	if(isSgInitializedName(node)) {
		SgInitializedName* iname = isSgInitializedName(node);
		
		//Is this really needed?
		//if(isSgCtorInitializerList(iname->get_declaration()))
		//	return NULL;
	
		if(iname->get_scope() == NULL || (iname->get_prev_decl_item()  != NULL && strcmp(iname->get_prev_decl_item()->sage_class_name(),"SgNode") == 0))
			return NULL;
		 
		return iname->search_for_symbol_from_symbol_table();
	

	}

	//Declarations.
	if(isSgDeclarationStatement(node))
		return handleDeclaration(isSgDeclarationStatement(node));
	
	//Expressions.
	if(isSgExpression(node))
		return handleExpression(isSgExpression(node));

	
	//Etc.
	if( isSgLabelStatement(node) ) return isSgLabelStatement(node)->get_symbol_from_symbol_table();
 

	return NULL;
}



//deleteSymbol: removes the symbol from the table, and deallocates the symbol.
void deleteSymbol(SgSymbolTable* table, SgSymbol* symbol){
	ROSE_ASSERT(symbol);
	ROSE_ASSERT(table); //This function assumes that both the table and the symbol exist.
	#ifdef ASTDELETION_DEBUG
		printf("deleteSymbol: Symbol targeted for deletion.\n");
	#endif
	table->remove(symbol);
	delete symbol;
	#ifdef ASTDELETION_DEBUG
		printf("deleteSymbol: Deletion complete.\n");
	#endif
}




/**** CHECKING TO SEE WHETHER A SYMBOL CAN BE SAFELY DELETED ****/
/* A symbol is safe to delete when only one node, the node we are going to delete next, is         */
/* associated with it. To confirm this, we dispatch MemoryVisitor instances that traverse the      */
/* memory pool in search of usages of a given symbol. It is assumed that we will find at least one */
/* node associated with the symbol, and that is the node for which we called getAssociatedSymbol.  */
/* If we find any other usages of the symbol, then MemoryVisitor will report that it would be      */
/* unsafe to delete it.	For debugging purposes, a container is use to collect a list of all the    */
/* instances in which the symbol is used.							   */


enum VisitorStatus {Unknown,Safe,Unsafe};
typedef std::deque<SgNode*> NodeContainer; //Storage type for the match container, used for debugging purposes.

//MemoryVisitor: Visitor class that checks the memory pool for usages of a symbol.
class MemoryVisitor : public ROSE_VisitorPattern
	{
		private:
			//This container is used during the safety check to provide informative
			//output if the symbol basis cannot be deleted safely.
			NodeContainer* matches; 
			bool collectMatches; //Toggles the use of the container.



			SgSymbol* symbol;
			VisitorStatus status;
			
			//updateStatus: This function is called whenever a matching symbol is found. If one had not yet been seen, status becomes Safe.
			//If the symbol had already been seen before, then the status becomes Unsafe.
			void updateStatus(){
				switch(status){
					case Unknown: status = Safe; break; //We have seen one occurrence of the symbol. We believe it is safe to delete. 
					case Safe: status = Unsafe; break; //If we see that there is more than one occurrence of the symbol, we should not delete it.
					case Unsafe: status = Unsafe; break; //We have seen two or more occurrences of the symbol.
				}
			}

		public:
			//This is a constructor for the MemoryVisitor.
			MemoryVisitor(SgSymbol* s){
				ROSE_ASSERT(s != NULL);
				symbol = s;
				status = Unknown;
				collectMatches = false;
				matches = NULL;
			}

			//This second constructor allows the user to enable the
			//collection of nodes associated with the symbol.
			MemoryVisitor(SgSymbol* s, bool shouldCollectMatches){
				ROSE_ASSERT(s != NULL);
				symbol = s;
				status = Unknown;
				collectMatches = shouldCollectMatches;
				if(collectMatches)
					matches = new NodeContainer();
				else
					matches = NULL;
			}


			//isSafeToDelete: After traversal, this function reports whether the given symbol is safe to delete.
			//If this function is called prematurely or if no matches were found during the traversal of the memory pool,
			//an assertion will fail.
			bool isSafeToDelete(){
				if(status == Unknown){
					#ifdef ASTDELETION_MEMORY_VISITOR_DEBUG
						printf("isSafeToDelete: status unknown. Premature call of function or no matches found.\n");
					#endif
					ROSE_ASSERT(status != Unknown);
				} else if(status == Safe)
					return true;
				return false;
			}


			//The visit function for the class.
			void visitDefault(SgNode* node) {

				SgSymbol* nSym = getAssociatedSymbol(node);
				if(nSym){
					if(symbol == nSym){
						#ifdef ASTDELETION_MEMORY_VISITOR_DEBUG
							printf("MemoryVisitor: matching symbol found in pool.\n");
						#endif
						updateStatus();
						if(collectMatches)
							matches->push_front(node);

					}
				}
				
			}


			//getMatches: Returns the list of nodes whose associated symbol is the symbol passed to the MemoryVisitor.
			//This should be called only after the traversal is complete and only if collectMatches was set to true.
			NodeContainer* getMatches(){
				ROSE_ASSERT(collectMatches == true && matches != NULL);
				return matches;
			}

};



/**** VERIFYING THAT A DELETION OPERATION IS SAFE ****/
/* Choice. It's the best part of being a real person, but, if used incorrectly, can also be the    */
/* most dangerous. For example, deleting a node that is the basis for a symbol when that symbol    */
/* is used elsewhere is a terrible choice. SafetyVisitor exists to prevent the user from making    */
/* such choices. The class performs a pre-deletion traversal of the AST to confirm that the 	   */
/* operation will not result in an AST that is invalid.						   */


//SafetyVisitor: Visitor class for the pre-deletion safety check traversal.
class SafetyVisitor : public AstSimpleProcessing, ROSE_VisitTraversal
{
	private:
	bool safeToProceed;

	public:

	//Constructor for the SafetyVisitor class.
	SafetyVisitor(){
		safeToProceed = true; //We assume that a deletion operation is safe unless we have evidence that indicates otherwise.
	}

	//isSafeToProceed: Accessor function.
	bool isSafeToProceed(){
		return safeToProceed;	
	}

	//The visit function for the class.
	void visit (SgNode* node)
        {
		if(SI::getProject()->get_verbose() <= 0 && !safeToProceed){
			//If we do not intend on providing additional output and we know it is not safe to continue, we need check no more.
			//printf("deleteAST: The safety check determined that the deletion cannot be performed.\n");
               	 	//ROSE_ASSERT(safeToProceed); //TMP
			return;
		}

		ROSE_ASSERT(node != NULL);
		#ifdef ASTDELETION_SAFETYCHECK_DEBUG
			printf("node: %s\n", node->sage_class_name());
		#endif


		SgSymbol* symbol = getAssociatedSymbol(node);

		if(isSgSymbol(symbol) && node == symbol->get_symbol_basis()){
			#ifdef ASTDELETION_SAFETYCHECK_DEBUG
				printf("deleteAST: Dispatching MemoryVisitor for symbol (%s).\n",symbol->sage_class_name());
			#endif
			MemoryVisitor visitor(symbol,true);
			traverseMemoryPoolVisitorPattern(visitor);
			#ifdef ASTDELETION_SAFETYCHECK_DEBUG
				printf("deleteAST: MemoryVisitor traversal complete.\n");
			#endif
			bool safe  = visitor.isSafeToDelete();
			if(!safe){
				safeToProceed = false;
				if (SI::getProject()->get_verbose() > 0) {
					printf("deleteAST: Safety check violation. The following node cannot be deleted safely because it is the basis for a symbol that is used elsewhere.\n");
					printNodeExt(node);
				}

				NodeContainer* matches = visitor.getMatches();
				if (SI::getProject()->get_verbose() > 0) {
					printf("deleteAST: %d other nodes are associated with this node's associated symbol.\n",matches->size()-1);
				}


				if (SI::getProject()->get_verbose() > 1) {
					NodeContainer::iterator it = matches->begin();
					while(it != matches->end()){
						SgNode* current = *it;
						if(current != node){
							if(isSgSymbol(current))
								printf("node: %s\n", node->sage_class_name());
							else
								printNodeExt(current);
						}
						it++;
					}
				}

			}
		}
	}
};



//DeletionMark: This AstAttribute indicates that a node will be deleted after the traversal is complete because it is not safe to do so during the traversal.
//More specifically, this is used to mark scopes, which we do not want to delete until after the traversal is complete because we may need to access their
//symbol tables.
class DeletionMark : public AstAttribute {
	public:
	
	DeletionMark()
	{};
};



/**** DELETION ****/
/* Below is the deletion routine proper, the heart of the deleteAST algorithm. The DeleteAST	   */
/* visitor traverses the selected subtree in post-order, cleanly and thoroughly deleting each node */
/* and the symbols that are associated with them.						   */



//DeleteAST: The is the visitor for the deletion traversal.
class DeleteAST : public AstSimpleProcessing, ROSE_VisitTraversal
	{
        	public:

                        void visit (SgNode* node)
                        {

				ROSE_ASSERT(node != NULL);
                                #ifdef ASTDELETION_DEBUG
                                        printf("DeleteAST: Deleting node.\n");
                                #endif

                                #if defined(DELETION_DEBUG) || defined(ASTDELETION_DEBUG_MINIMAL)
  					printf("node: %s\n", node->sage_class_name());
                                #endif


				//First, we check to see if the node has an associated symbol.
				SgSymbol* symbol = getAssociatedSymbol(node);

				if(isSgSymbol(symbol)){
					#ifdef ASTDELETION_DEBUG
						printf("deleteAST: Dispatching MemoryVisitor for symbol (%s).\n",symbol->sage_class_name());
					#endif

					//We instantiate a MemoryVisitor to check to see whether the symbol can be safely deleted.
					MemoryVisitor visitor(symbol);
					traverseMemoryPoolVisitorPattern(visitor);

					#ifdef ASTDELETION_DEBUG
						printf("deleteAST: MemoryVisitor traversal complete.\n");
					#endif
					bool safe  = visitor.isSafeToDelete();

					if(safe){
						//If the symbol is safe to delete according to the criteria of the MemoryVisitor, we do so here.

						#ifdef ASTDELETION_DEBUG
							printf("deleteAST: symbol is safe to delete.\n");
						#endif
						if(isSgVarRefExp(node) || isSgFunctionRefExp(node) || isSgMemberFunctionRefExp(node) || isSgClassNameRefExp(node) || isSgThisExp(node)) {
							delete symbol;
							#ifdef ASTDELETION_DEBUG
								printf("deleteAST: symbol deleted without going to symbol table.\n");
							#endif
						} else {
							ROSE_ASSERT(symbol->get_symbol_basis() != NULL);							
							SgSymbolTable* table = symbol->get_scope()->get_symbol_table();
							if(table){
								deleteSymbol(table,symbol);
								#ifdef ASTDELETION_DEBUG
									printf("deleteAST: symbol deleted.\n");
								#endif
							}


						}
					} else {
						#ifdef ASTDELETION_DEBUG
							printf("deleteAST: symbol is NOT safe to delete.\n");
						#endif
						
					}

				}


				if(isSgInitializedName(node)){
                                        //remove SgVariableDefinition
                                        SgDeclarationStatement* def;
					def =  ((SgInitializedName *)node)->get_definition();
                                        if(isSgVariableDefinition(def)){
						
						#ifdef ASTDELETION_CLEANUP_DEBUG
							printf("deleteAST: deleting definition (%s).\n",def->sage_class_name());
                                                #endif
						delete def;
						#ifdef ASTDELETION_CLEANUP_DEBUG
                                                	printf("deleteAST: A SgVariableDefinition was deleted\n");
						#endif
					} 
                                }

				if(isSgScopeStatement(node)){
					#ifdef ASTDELETION_DEBUG
						printf("DeleteAST: Current node is an SgScopeStatement. Deletion will be done after the traversal.\n");
					#endif
					node->addNewAttribute("DELETEMARK", new DeletionMark()); //Mark the node so we know to delete it later.
					return;

				}
				
				delete node;
				#ifdef ASTDELETION_DEBUG
					printf("DeleteAST: Node deleted.\n");
				#endif
			};


	};

//deleteMarkedScopes: Deletes SgScopeStatement nodes that have been marked for deletion during the traversal.
void deleteMarkedScopes(){
	class ScopeTraversal : public ROSE_VisitTraversal
        {
          public:
               void visit ( SgNode* node)
                  {
                    SgScopeStatement* scope = isSgScopeStatement(node);
                    if (scope != NULL)
                       {
				if(scope->getAttribute("DELETEMARK")){
					delete scope;
				}
                       }
                  };

              virtual ~ScopeTraversal() {};
        };

	ScopeTraversal scopeTraversal;
	scopeTraversal.traverseMemoryPool();

}


#if 0
bool isTypeUsed(SgType* ptr){
	if(!ptr)
		return false;

	if(isSgPointerType(ptr) || isSgReferenceType(ptr) || isSgModifierType(ptr)){
		if(isSgModifierType(ptr))
			return isTypeUsed(isSgModifierType(ptr)->get_base_type());
		else
			return isTypeUsed(ptr->dereference());
	}

	if(isSgNamedType(ptr)){
		SgNamedType* named_ptr = isSgNamedType(ptr);
		SgDeclarationStatement* decl = named_ptr->getAssociatedDeclaration();
		if(!decl){
			return false;
		} else if(!isSgScopeStatement(decl->get_scope())) {
			//delete decl;
			return false; //Is this correct?
		}
	}

	if(isSgFunctionType(ptr)){


	}


	return true;
}


std::vector<SgType*> generateTypeList(){
	class TypeTraversal : public ROSE_VisitTraversal
        {
          public:
               std::vector<SgType*> typeList;
               void visit ( SgNode* node)
                  {
                    SgType* type = isSgType(node);
                    if (type != NULL)
                       {
                         typeList.push_back(type);
                       }
                  };

              virtual ~TypeTraversal() {}
        };

	TypeTraversal typeTraversal;
	typeTraversal.traverseMemoryPool();
	
	return typeTraversal.typeList;
}

void removeUnusedTypes(){
	std::vector<SgType*> typeList = generateTypeList();
	#ifdef ASTDELETION_TYPE_REMOVAL_DEBUG
		std::cout << "SgType count (before):" << typeList.size() << std::endl;
	#endif

	int typeDeleteCount = 0;
	for (std::vector<SgType*>::iterator it = typeList.begin() ; it != typeList.end(); ++it){
		SgType* t = *it;
		if(!isTypeUsed(t)){
			typeDeleteCount++;

			delete t->get_typedefs();
			delete t->get_modifiers();
			delete t;
		}
	}	
	printf("type delete count: %d\n",typeDeleteCount);

}
#endif


};



/**** DELETION ROUTINE ****/
/* Below is the deleteAST function called by the user. The algorithm is fairly straightforward.    */
/* First, a SafetyVisitor is deployed to the site of the deletion to confirm that the deletion can */
/* proceed. Once the paperwork is completed, a DeleteAST visitor is employed to traverse the AST   */
/* and delete the targeted nodes. Finally, a pass is made over the memory pool to find and remove  */
/* any scopes that were scheduled for deletion; it is necessary that we handle the scopes          */
/* separately to retain their symbol tables throughout the main deletion phase.			   */


void SageInterface::deleteAST ( SgNode* n )
   {
	ROSE_ASSERT(n != NULL);

	
	ASTDeletionSupport::SafetyVisitor safetyChecker;
        safetyChecker.traverse(n,postorder);
	

	//If -rose:verbose is not set and we find that it is not safe to proceed during the traversal, 
	//an assertion in the visit function will terminate the program before we reach this point.
	if(!safetyChecker.isSafeToProceed()){
		printf("deleteAST: The safety check determined that the deletion cannot be performed.\n");
		ROSE_ASSERT(safetyChecker.isSafeToProceed());
	}
	

	ASTDeletionSupport::DeleteAST deleteTree;
        deleteTree.traverse(n,postorder);

	#if 0
	ASTDeletionSupport::removeUnusedTypes();
	#endif

	ASTDeletionSupport::deleteMarkedScopes();

   }
