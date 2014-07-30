#include "rose.h"
#include "wholeAST.h"
#include <iostream>
#include <cstdlib>
#include <vector>
#include <deque>
#include <map>
#include <utility>
namespace SI = SageInterface;

//#define ASTDELETION_DEBUG_MINIMAL
//#define ASTDELETION_DEBUG
//#define ASTDELETION_MEMORY_VISITOR_DEBUG
//#define ASTDELETION_CLEANUP_DEBUG
//#define ASTDELETION_TYPE_REMOVAL_DEBUG
//#define ASTDELETION_SAFETYCHECK_DEBUG

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
	
	SgSymbol* symbol = decl_to_search->search_for_symbol_from_symbol_table();
	
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
		

		//Now that we don't do this lookup in the middle of our deletion, we can probably take checks like these out.
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


class DeletionAnnotation : public AstAttribute {

	public:

	bool isTraversed; //This is true except for special cases (e.g. some first non-defining declarations).

	DeletionAnnotation() { isTraversed = true; };

	DeletionAnnotation(bool v) { isTraversed = v; };
	
};




//SafetyVisitor: Visitor class for the pre-deletion safety check traversal.
class SafetyVisitor : public AstSimpleProcessing
{
	private:
	bool safeToProceed;
	std::multimap<SgSymbol*, SgNode*>* matchMap;
	std::deque<SgSymbol*>* symbolList;
	public:

	//Constructor for the SafetyVisitor class.
	SafetyVisitor(){
		safeToProceed = true; //We assume that a deletion operation is safe unless we have evidence that indicates otherwise.
		matchMap = new std::multimap<SgSymbol*, SgNode*>();	
		symbolList = new std::deque<SgSymbol*>();
	}	

	//isSafeToProceed: Accessor function.
	bool isSafeToProceed(){
		return safeToProceed;	
	}

	//The visit function for the class.
	void visit (SgNode* node)
        {
		ROSE_ASSERT(node != NULL);
		#ifdef ASTDELETION_SAFETYCHECK_DEBUG
			printf("node: %s\n", node->sage_class_name());
		#endif

		SgSymbol* symbol = getAssociatedSymbol(node);
		
		if(symbol && matchMap->find(symbol) == matchMap->end()){
			symbolList->push_front(symbol);

			#ifdef ASTDELETION_SAFETYCHECK_DEBUG
				printf("deleteAST: Dispatching MemoryVisitor for symbol (%s).\n",symbol->sage_class_name());
			#endif

			SgSymbol* symToSearch = symbol;
			if(isSgAliasSymbol(symToSearch))
				symToSearch = isSgAliasSymbol(symToSearch)->get_base();


			MemoryVisitor visitor(symToSearch,true);
                        traverseMemoryPoolVisitorPattern(visitor);
			NodeContainer* matches = visitor.getMatches();
			NodeContainer::iterator it = matches->begin();
			while(it != matches->end()){
				SgNode* current = *it;
				matchMap->insert(std::pair<SgSymbol*,SgNode*>(symbol,current));
				it++;
                        }
		}

		//Special case for handling non-defining declarations that ought to be deleted but aren't going to be traversed.
		if(isSgDeclarationStatement(node)){
			SgDeclarationStatement* decl = isSgDeclarationStatement(node);
			SgDeclarationStatement* fndd = decl->get_firstNondefiningDeclaration();
			if(decl != fndd && fndd && fndd->get_firstNondefiningDeclaration() == fndd){
				if(!fndd->attributeExists("DELETION_ANNOTATION") && fndd->get_scope()->attributeExists("DELETION_ANNOTATION")) {
					printf("Marking %s.\n",fndd->sage_class_name()); //REMOVEME
					fndd->addNewAttribute("DELETION_ANNOTATION", new DeletionAnnotation(false));
				}
			}
		}

		node->addNewAttribute("DELETION_ANNOTATION", new DeletionAnnotation());
	}


	bool arrayTypeExprCheck(SgNode* node){
		if(!node)
			return false;
		if(isSgArrayType(node))
			return true;
		SgNode* parent = node->get_parent();
		return arrayTypeExprCheck(parent);
	}


	void atTraversalEnd() {
		std::multimap<SgSymbol*, SgNode*>::iterator it;
		for(it=matchMap->begin(); it!=matchMap->end(); ++it){
			SgSymbol* sym = (*it).first;
			SgNode* node = (*it).second;

			if(sym->get_symbol_basis()->getAttribute("DELETION_ANNOTATION")){
				ROSE_ASSERT(node->getAttribute("DELETION_ANNOTATION") || arrayTypeExprCheck(node));
			}

		} 

		std::deque<SgSymbol*>::iterator slIterator = symbolList->begin();	
		while(slIterator != symbolList->end()){
			SgSymbol* sym = *slIterator;
			if(sym->get_symbol_basis()->getAttribute("DELETION_ANNOTATION")){
				SgScopeStatement* scope = sym->get_scope();
				SgSymbolTable* table = scope->get_symbol_table();
                        	deleteSymbol(table,sym);
			}

			++slIterator;
		}

	}

};



#if 0
//DeletionMark: This AstAttribute indicates that a node will be deleted after the traversal is complete because it is not safe to do so during the traversal.
//More specifically, this is used to mark scopes, which we do not want to delete until after the traversal is complete because we may need to access their
//symbol tables.
class DeletionMark : public AstAttribute {
	public:
	DeletionMark()
	{};
};
#endif




/**** DELETION ****/
/* Below is the deletion routine proper, the heart of the deleteAST algorithm. The DeleteAST	   */
/* visitor traverses the selected subtree in post-order, cleanly and thoroughly deleting each node */
/* and the symbols that are associated with them.						   */



//DeleteAST: The is the visitor for the deletion traversal.
class DeleteAST : public AstSimpleProcessing //, ROSE_VisitTraversal
	{
        	public:


		void clean(SgNode* node){
			ROSE_ASSERT(node != NULL);

                        #if defined(ASTDELETION_DEBUG) || defined(ASTDELETION_DEBUG_MINIMAL)
  				printf("deleteAST: node: %s\n", node->sage_class_name());
                        #endif

			Sg_File_Info* info = node->get_file_info();
			if(info)
				delete info;
				
			if(isSgLocatedNode(node) && node->attributeExists("DELETION_ANNOTATION")){
				AstAttribute* attribute = node->getAttribute("DELETION_ANNOTATION");
				ROSE_ASSERT(attribute != NULL);
				node->removeAttribute("DELETION_ANNOTATION");
				delete attribute;
			}
			delete node;


		}


			
		void visit(SgNode* node){

			if(isSgDeclarationStatement(node)) {

				//Check to see if there is a non-defining declaration that needs to be deleted.
				SgDeclarationStatement* fndd = isSgDeclarationStatement(node)->get_firstNondefiningDeclaration();
				if(node != fndd && fndd && fndd->get_firstNondefiningDeclaration() == fndd){
					DeletionAnnotation* attribute = (DeletionAnnotation*) fndd->getAttribute("DELETION_ANNOTATION");
					if(attribute && !attribute->isTraversed ){
						visit(fndd);
					}
				}


				if(isSgTemplateDeclaration(node)){
                                        SgTemplateParameterPtrList tempparams = isSgTemplateDeclaration(node)->get_templateParameters();
                                        SgTemplateParameterPtrList::iterator current = tempparams.begin();
                                        while(current != tempparams.end()) {
                                                SgTemplateParameter* tempparam = isSgTemplateParameter(*current);
                                                if(tempparam){
                                                        visit(tempparam);
                                                }
                                                ++current;
                                        }
				}


                                if(isSgTemplateInstantiationDecl(node)){
                                        SgTemplateArgumentPtrList tempargs = isSgTemplateInstantiationDecl(node)->get_templateArguments();

                                        SgTemplateArgumentPtrList::iterator current = tempargs.begin();
                                        while(current != tempargs.end()) {
                                                SgTemplateArgument* temparg = isSgTemplateArgument(*current);
                                                if(temparg){
                                                        visit(temparg);
                                                }
                                                ++current;
                                        }
                                }

				if(isSgScopeStatement(node)){

					if(isSgClassDefinition(node)){
						SgBaseClassPtrList baseclassptrs = isSgClassDefinition(node)->get_inheritances();
                                        	SgBaseClassPtrList::iterator current = baseclassptrs.begin();
                                        	while(current != baseclassptrs.end()) {
                                                	SgBaseClass* baseclass = isSgBaseClass(*current);
                                                	if(baseclass){
                                                        	visit(baseclass);
                                                	}
                                                	++current;
                                        	}
					}

					if(isSgNamespaceDefinitionStatement(node)){
						SgNamespaceDefinitionStatement* nds = isSgNamespaceDefinitionStatement(node);
						
						if(nds->get_nextNamespaceDefinition() != NULL)
							visit(nds->get_nextNamespaceDefinition());

					}

					SgSymbolTable* symboltable = isSgScopeStatement(node)->get_symbol_table();
					SgTypeTable* typetable = isSgScopeStatement(node)->get_type_table();
					visit(symboltable);
					visit(typetable);
				}

			} else if(isSgInitializedName(node)){

                        	SgDeclarationStatement* def = isSgInitializedName(node)->get_definition();
				if(isSgVariableDefinition(def))
					visit(def);

			} else if(isSgProject(node)) {
				visit(isSgProject(node)->get_directoryList());

				SgTypeTable* globaltypetable = SgNode::get_globalTypeTable();
				visit(globaltypetable);
				
				SgFunctionTypeTable* globalfunctiontypetable = SgNode::get_globalFunctionTypeTable();
				visit(globalfunctiontypetable);


			} else if(isSgSymbolTable(node)){
				std::set<SgNode*> remainingSymbols = isSgSymbolTable(node)->get_symbols();
				for (std::set<SgNode*>::iterator it=remainingSymbols.begin(); it!=remainingSymbols.end(); ++it){
					SgSymbol* sym = isSgSymbol(*it);
					SgNode* basis = sym->get_symbol_basis();
					visit(basis);
					delete sym;
				}

			} else if(isSgTypeTable(node)){
				SgSymbolTable* symtable = isSgTypeTable(node)->get_type_table(); 
				std::set<SgNode*> remainingTypes = symtable->get_symbols();
				for (std::set<SgNode*>::iterator it=remainingTypes.begin(); it!=remainingTypes.end(); ++it){
					SgSymbol* sym = isSgSymbol(*it);
					SgType* type = sym->get_type();
					delete type->get_typedefs();
					delete type;
					delete sym;
				}
				clean(symtable);
				
			} else if(isSgFunctionTypeTable(node)) {
				SgSymbolTable* fttable = isSgFunctionTypeTable(node)->get_function_type_table();
				std::set<SgNode*> ftremainingSymbols = fttable->get_symbols();
				for (std::set<SgNode*>::iterator it=ftremainingSymbols.begin(); it!=ftremainingSymbols.end(); ++it){
					SgFunctionTypeSymbol* typeSym = isSgFunctionTypeSymbol(*it);
					SgFunctionType* type = isSgFunctionType(typeSym->get_type()); 
					delete type->get_argument_list();
					delete type->get_typedefs();
					delete type;
					delete typeSym;
				}
				clean(fttable);
			}

			clean(node);
	

			#if 0
                        void visit(SgNode* node)
                        {

				ROSE_ASSERT(node != NULL);
				printf("HAI!\n");
				//clean(node);
				return;

				#if 0
                                #ifdef ASTDELETION_DEBUG
                                        printf("DeleteAST: Deleting node.\n");
                                #endif

                                #if defined(ASTDELETION_DEBUG) || defined(ASTDELETION_DEBUG_MINIMAL)
  					printf("node: %s\n", node->sage_class_name());
                                #endif




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



				//Check to see if there is a non-defining declaration that needs to be deleted.
				if(isSgDeclarationStatement(node)){
					SgDeclarationStatement* decl = isSgDeclarationStatement(node);
					SgDeclarationStatement* fndd = decl->get_firstNondefiningDeclaration();
					if(decl != fndd && fndd && fndd->get_firstNondefiningDeclaration() == fndd){
						DeletionAnnotation* attribute = (DeletionAnnotation*) fndd->getAttribute("DELETION_ANNOTATION");
						if(attribute && !attribute->isTraversed ){
							delete attribute;
							delete fndd;
						}
					}

				}


				if(isSgTemplateDeclaration(node)){
                                        SgTemplateParameterPtrList tempparams = isSgTemplateDeclaration(node)->get_templateParameters();
                                        SgTemplateParameterPtrList::iterator current = tempparams.begin();
                                        while(current != tempparams.end()) {
                                                SgTemplateParameter* tempparam = isSgTemplateParameter(*current);
                                                if(tempparam){
                                                        delete tempparam;
                                                }
                                                ++current;
                                        }

				}

                                if(isSgTemplateInstantiationDecl(node)){
                                        SgTemplateArgumentPtrList tempargs = isSgTemplateInstantiationDecl(node)->get_templateArguments();

                                        SgTemplateArgumentPtrList::iterator current = tempargs.begin();
                                        while(current != tempargs.end()) {
                                                SgTemplateArgument* temparg = isSgTemplateArgument(*current);
                                                if(temparg){
                                                        delete temparg;
                                                }
                                                ++current;
                                        }
                                }


				if(isSgClassDefinition(node)){
					SgBaseClassPtrList baseclassptrs = isSgClassDefinition(node)->get_inheritances();
                                        SgBaseClassPtrList::iterator current = baseclassptrs.begin();
                                        while(current != baseclassptrs.end()) {
                                                SgBaseClass* baseclass = isSgBaseClass(*current);
                                                if(baseclass){
                                                        delete baseclass;
                                                }
                                                ++current;
                                        }
				}



				//BOOKMARK

				//#if 0
				if(isSgScopeStatement(node)){
					SgSymbolTable* symboltable = isSgScopeStatement(node)->get_symbol_table();
					std::set<SgNode*> remainingSymbols = symboltable->get_symbols();
					for (std::set<SgNode*>::iterator it=remainingSymbols.begin(); it!=remainingSymbols.end(); ++it){
						SgSymbol* sym = isSgSymbol(*it);
						SgNode* basis = sym->get_symbol_basis();
						visit(basis);
						delete *it;
					}
					delete symboltable;

					SgTypeTable* typetable = isSgScopeStatement(node)->get_type_table();
					std::set<SgNode*> remainingTypes = typetable->get_type_table()->get_symbols();
					for (std::set<SgNode*>::iterator it=remainingTypes.begin(); it!=remainingTypes.end(); ++it){
						SgSymbol* sym = isSgSymbol(*it);
						SgType* type = sym->get_type();
						delete type->get_typedefs();
						delete type;
						delete sym;
					}
					delete typetable;

					/*
					if(isSgNamespaceDefinitionStatement(node)){
						SgNamespaceDefinitionStatement* defstmt = isSgNamespaceDefinitionStatement(node);
						if(defstmt->get_namespaceDeclaration()->get_firstNondefiningDeclaration() ==	
				
					}
					*/

					/*
					if(isSgScopeStatement(node)->containsOnlyDeclarations()){
						SgDeclarationStatementPtrList declPtrList = isSgScopeStatement(node)->getDeclarationList();
						for(SgDeclarationStatementPtrList::iterator it=declPtrList.begin(); it!=declPtrList.end(); ++it){
							delete *it;
						} 
					}

					
					if(isSgGlobal(node)){
						SgDeclarationStatementPtrList declPtrList = isSgGlobal(node)->get_declarations();
						for(SgDeclarationStatementPtrList::iterator it=declPtrList.begin(); it!=declPtrList.end(); ++it){
							delete *it;
						} 
					}
					*/

				}
				//#endif


				if(isSgProject(node)){
					SgProject* p = isSgProject(node);

				}
	

				Sg_File_Info* info = node->get_file_info();
				if(info)
					delete info;
				
				if(node->attributeExists("DELETION_ANNOTATION")){
					AstAttribute* attribute = node->getAttribute("DELETION_ANNOTATION");
					ROSE_ASSERT(attribute != NULL);
					node->removeAttribute("DELETION_ANNOTATION");
					delete attribute;
				}
				delete node;
				#ifdef ASTDELETION_DEBUG
					printf("DeleteAST: Node deleted.\n");
				#endif
				#endif
				#endif
			};

	};

#if 0
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
        safetyChecker.traverse(n,preorder);
	
	
	

	ASTDeletionSupport::DeleteAST deleteTree;
        deleteTree.traverse(n,postorder);

	#if 0
	ASTDeletionSupport::removeUnusedTypes();
	#endif
	
	#if 0
	ASTDeletionSupport::deleteMarkedScopes();
	#endif
   }
