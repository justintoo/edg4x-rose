#include "sage3basic.h"
#include "ASTDeletion.h"

//#define ASTDELETION_DEBUG_MINIMAL
//#define ASTDELETION_DEBUG
//#define ASTDELETION_MEMORY_VISITOR_DEBUG
//#define ASTDELETION_CLEANUP_DEBUG
//#define ASTDELETION_TYPE_REMOVAL_DEBUG
//#define ASTDELETION_SAFETYCHECK_DEBUG


void ASTDeletionSupport::printNode(SgNode* node) {
    printf("node: %s = %s\n", node->class_name().c_str(), node->unparseToString().c_str());
}

void ASTDeletionSupport::printNodeExt(SgNode* node) {
    Sg_File_Info* File = node->get_file_info();
    if(File != NULL){
        printf("(File: %s, line:%d, column:%d) %s = %s\n", File->get_filenameString().c_str(),
        File->get_line(),
        File->get_col(),
        node->class_name().c_str(),
        node->unparseToString().c_str());
    } else {
        printNode(node);
    }
}


SgNode* ASTDeletionSupport::reachProject(SgNode* node) {
    if(node == NULL)
         return NULL;
    else if(isSgProject(node))
         return node;
    else if(node->get_parent() == NULL)
         return node;
    else
         return reachProject(node->get_parent());


}

SgSymbol* ASTDeletionSupport::handleDeclaration(SgDeclarationStatement* decl){
    ROSE_ASSERT(decl != NULL);
    if(!decl->hasAssociatedSymbol())
        return NULL;

    SgDeclarationStatement* decl_to_search = decl;

    //From the ROSE documentation for SgMemberFunctionDeclaration nodes (circa July 2014):
    //The scope can at times be that of the global scope, when this happens users should access the scope through 
    //get_firstNondefiningDeclaration(). This appears to be a bug internally.   
    if(isSgMemberFunctionDeclaration(decl))
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

    //TMPTEST
    if((isSgTemplateDeclaration(decl_to_search) || isSgFunctionDeclaration(decl_to_search)) && !decl_to_search->get_declaration_associated_with_symbol()){
         printf("deleteAST: Warning! A template declaration and/or function declaration returned NULL when queried for the declaration associated with its symbol. This indicates a flaw in the construction of the AST.\n");
         return NULL;
    }
    if(isSgNamespaceAliasDeclarationStatement(decl_to_search)){
         SgSymbol* s = decl_to_search->get_symbol_from_symbol_table();
         if(s == NULL)
             printf("deleteAST: Warning! A namespace alias declaration statement did not have a corresponding namespace symbol."); 
         else
             return s;
    }

    if(isSgUseStatement(decl_to_search) || isSgNamelistStatement(decl_to_search) || isSgFortranIncludeLine(decl_to_search) || isSgCommonBlock(decl_to_search) || isSgFormatStatement(decl_to_search) || isSgImplicitStatement(decl_to_search) || 
    isSgAttributeSpecificationStatement(decl_to_search) || isSgJavaPackageStatement(decl_to_search) || isSgJavaImportStatement(decl_to_search)) {
        return NULL;
    }

    SgSymbol* symbol = decl_to_search->search_for_symbol_from_symbol_table();
    
    return symbol;
}


SgSymbol* ASTDeletionSupport::handleExpression(SgExpression* expr){

    //reference expressions
    if(isSgVarRefExp(expr)) return isSgVarRefExp(expr)->get_symbol();
    if(isSgFunctionRefExp(expr)) return isSgFunctionRefExp(expr)->get_symbol();
    if(isSgMemberFunctionRefExp(expr)) return isSgMemberFunctionRefExp(expr)->get_symbol();
    if(isSgLabelRefExp(expr)) return isSgLabelRefExp(expr)->get_symbol();
    if(isSgClassNameRefExp(expr)) return isSgClassNameRefExp(expr)->get_symbol();

    //etc.
    if(isSgThisExp(expr)) return isSgThisExp(expr)->get_class_symbol();
    if(isSgUserDefinedBinaryOp(expr)) return isSgUserDefinedBinaryOp(expr)->get_symbol(); 

    return NULL;

}


SgSymbol* ASTDeletionSupport::getAssociatedSymbol(SgNode* node){
    ROSE_ASSERT(node != NULL);

    //Initialized names.
    if(isSgInitializedName(node)) {
        SgInitializedName* iname = isSgInitializedName(node);

        //Now that we don't do this lookup in the middle of our deletion, we can probably take checks like these out.
        if(iname->get_scope() == NULL || (iname->get_prev_decl_item()  != NULL && strcmp(iname->get_prev_decl_item()->class_name().c_str(),"SgNode") == 0))
            return NULL;
        

        //Note: Added in due to issue with Fortran code.
        if( iname->get_prev_decl_item() == iname )
            return iname->get_symbol_from_symbol_table();
 
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


void ASTDeletionSupport::deleteSymbol(SgSymbolTable* table, SgSymbol* symbol){
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

void ASTDeletionSupport::deleteType(SgType* type){
    if(type == NULL)
        return;
    if(isSgFunctionType(type))
        delete isSgFunctionType(type)->get_argument_list();                 
    delete type->get_typedefs();
    delete type;       
}

ASTDeletionSupport::MemoryVisitor::MemoryVisitor(SgSymbol* s){
    ROSE_ASSERT(s != NULL);
    symbol = s;
    matches = new NodeContainer();
}

ASTDeletionSupport::MemoryVisitor::~MemoryVisitor(){
        delete matches;
}

void ASTDeletionSupport::MemoryVisitor::visitDefault(SgNode* node) {
    ROSE_ASSERT(node != NULL);

    SgSymbol* nSym = getAssociatedSymbol(node);
    if(nSym){
        if(symbol == nSym){
            #ifdef ASTDELETION_MEMORY_VISITOR_DEBUG
                printf("MemoryVisitor: matching symbol found in pool.\n");
            #endif
            matches->push_front(node);

        }
    }
}

ASTDeletionSupport::NodeContainer* ASTDeletionSupport::MemoryVisitor::getMatches(){

    if(matches->size() == 0){
        //If no matches were found, then how could we have found the symbol in the first place?
        //This is a sanity check.
        #ifdef ASTDELETION_MEMORY_VISITOR_DEBUG
            printf("MemoryVisitor: no matches were found for the symbol.\n");
        #endif  
        ROSE_ASSERT(matches->size() != 0);
    }
    return matches;
}



ASTDeletionSupport::SafetyVisitor::SafetyVisitor(){
    safeToProceed = true; //We assume that a deletion operation is safe unless we have evidence that indicates otherwise.
    matchMap = new std::multimap<SgSymbol*, SgNode*>(); 
    symbolList = new NodeContainer();
}

ASTDeletionSupport::SafetyVisitor::~SafetyVisitor(){
    delete matchMap;
    delete symbolList;
}  

bool ASTDeletionSupport::SafetyVisitor::isSafeToProceed(){
    return safeToProceed;   
}

void ASTDeletionSupport::SafetyVisitor::visit (SgNode* node) {
    ROSE_ASSERT(node != NULL);
    #ifdef ASTDELETION_SAFETYCHECK_DEBUG
        printf("node: %s\n", node->class_name().c_str());
    #endif
    
    //Check to see whether the node has a symbol associated with it.
    SgSymbol* symbol = getAssociatedSymbol(node);
    
    if(symbol && symbol->get_symbol_basis() == node && matchMap->find(symbol) == matchMap->end()){
        symbolList->push_front(symbol);

        #ifdef ASTDELETION_SAFETYCHECK_DEBUG
            printf("deleteAST: Dispatching MemoryVisitor for symbol (%s).\n",symbol->class_name().c_str());
        #endif

        SgSymbol* symToSearch = symbol;

        if(isSgAliasSymbol(symToSearch)) {
            symToSearch = isSgAliasSymbol(symToSearch)->get_base();
        }

        MemoryVisitor visitor(symToSearch);
        traverseMemoryPoolVisitorPattern(visitor);
        NodeContainer* matches = visitor.getMatches();
        NodeContainer::iterator it = matches->begin();
        while(it != matches->end()){
            SgNode* current = *it;
            matchMap->insert(std::pair<SgSymbol*,SgNode*>(symbol,current));
            it++;
        }
    }
    
    //Mark the node for deletion.
    if(isSgLocatedNode(node) && !node->attributeExists("DELETION_ANNOTATION"))
         node->addNewAttribute("DELETION_ANNOTATION", new DeletionAnnotation());

}

void ASTDeletionSupport::SafetyVisitor::atTraversalEnd() {
    std::multimap<SgSymbol*, SgNode*>::iterator it;
    for(it=matchMap->begin(); it!=matchMap->end(); ++it){
        SgSymbol* sym = (*it).first;
        SgNode* node = (*it).second;
        if(sym->get_symbol_basis()->attributeExists("DELETION_ANNOTATION")){
            if(!(node->attributeExists("DELETION_ANNOTATION") ||  !isSgProject(reachProject(node)) ||  SageInterface::getScope(node)->attributeExists("DELETION_ANNOTATION"))) {
                 safeToProceed = false;
                 #ifdef ASTDELETION_SAFETYCHECK_DEBUG
                       printf("Deletion Safety Check Violation: Want to delete the basis for a symbol (%s), but the symbol is used by another node (%s) that will not be deleted.\n",sym->get_symbol_basis()->class_name().c_str(), node->class_name().c_str());
                 #endif
            }
        }
    } 

    NodeContainer::iterator slIterator = symbolList->begin();   
    while(slIterator != symbolList->end()){
        SgSymbol* sym = isSgSymbol(*slIterator);
        if(sym->get_symbol_basis()->attributeExists("DELETION_ANNOTATION")){
            SgScopeStatement* scope = sym->get_scope();
            SgSymbolTable* table = scope->get_symbol_table();
                        deleteSymbol(table,sym);
        }

        ++slIterator;
    }
}

void ASTDeletionSupport::DeleteAST::clean(SgNode* node){
    ROSE_ASSERT(node != NULL);

    #if defined(ASTDELETION_DEBUG) || defined(ASTDELETION_DEBUG_MINIMAL)
        printf("deleteAST: node: %s\n", node->class_name().c_str());
    #endif

    if(isSgLocatedNode(node) && node->attributeExists("DELETION_ANNOTATION")){
AstAttribute* attribute = node->getAttribute("DELETION_ANNOTATION");
node->removeAttribute("DELETION_ANNOTATION");
        delete attribute;
    }
    
    delete node;
}

void ASTDeletionSupport::DeleteAST::visit(SgNode* node){
    if(isSgProject(node)) {

        SgTypeTable* globaltypetable = SgNode::get_globalTypeTable();
        visit(globaltypetable);
        
        SgFunctionTypeTable* globalfunctiontypetable = SgNode::get_globalFunctionTypeTable();
        visit(globalfunctiontypetable);


    } else if(isSgSymbolTable(node)){
        
        std::set<SgNode*> remainingSymbols = isSgSymbolTable(node)->get_symbols();
        for (std::set<SgNode*>::iterator it=remainingSymbols.begin(); it!=remainingSymbols.end(); ++it){
            SgSymbol* sym = isSgSymbol(*it);
            if(sym) {
                 delete sym;
            }
        }
    } else if(isSgTypeTable(node)){

        SgSymbolTable* symtable = isSgTypeTable(node)->get_type_table(); 
        
        std::set<SgNode*> remainingTypes = symtable->get_symbols();
        for (std::set<SgNode*>::iterator it=remainingTypes.begin(); it!=remainingTypes.end(); ++it){
            SgSymbol* sym = isSgSymbol(*it);
            if(sym) {
                 deleteType(sym->get_type());
                 delete sym;
            }
        }
        
        clean(symtable);
        
    } else if(isSgFunctionTypeTable(node)) {
        SgSymbolTable* fttable = isSgFunctionTypeTable(node)->get_function_type_table();
        
        std::set<SgNode*> ftremainingSymbols = fttable->get_symbols();
        for (std::set<SgNode*>::iterator it=ftremainingSymbols.begin(); it!=ftremainingSymbols.end(); ++it){
            SgFunctionTypeSymbol* typeSym = isSgFunctionTypeSymbol(*it);
            if(typeSym){
                 deleteType(typeSym->get_type());
                 delete typeSym;
            }
        }
        
        clean(fttable);
    }

    std::vector< std::pair<SgNode *, std::string > > ptrs = node->returnDataMemberPointers();
    std::vector< std::pair<SgNode *, std::string > >::iterator it;
    for(it = ptrs.begin(); it != ptrs.end(); it++){
         std::pair<SgNode *, std::string > p = *it;
         SgNode* n = p.first;
         if(n != NULL && n->get_parent() == node && !isSg_File_Info(n)){
              visit(n);
         }
    }

    clean(node);

};



ASTDeletionSupport::CleanupVisitor::CleanupVisitor() {
    nodes = new NodeContainer();
}

ASTDeletionSupport::CleanupVisitor::~CleanupVisitor() {
    delete nodes;
}


void ASTDeletionSupport::CleanupVisitor::visitDefault(SgNode* node){
     if(node->variantT() == V_SgNode)
          return;
     SgNode* urnode = reachProject(node);
     if(!(isSgProject(urnode) || isSgType(urnode))) {
               nodes->push_front(node);
          }
}

void ASTDeletionSupport::CleanupVisitor::finish() {
    std::map<std::string,int> countMap;
    for(NodeContainer::iterator it = nodes->begin(); it != nodes->end(); it++){
         SgNode* n = *it;
         if(n->variantT() == V_SgNode)
              continue;
         #ifdef ASTDELETION_CLEANUP_DEBUG    
              if(!countMap[n->class_name()])
                   countMap[n->class_name()] = 1;
              else
                   countMap[n->class_name()] += 1;
         #endif
         delete n;
    }

    #ifdef ASTDELETION_CLEANUP_DEBUG
         printf("deleteAST: Cleanup results.\n");
         for(std::map<std::string,int>::iterator it = countMap.begin(); it != countMap.end(); it++){
              printf("     %s : %d\n",(*it).first.c_str(),(*it).second);
         }
    #endif



}

void SageInterface::cleanMemoryPool(){
    ASTDeletionSupport::CleanupVisitor cleanup;
    traverseMemoryPoolVisitorPattern(cleanup);
    cleanup.finish();
}


void SageInterface::deleteAST ( SgNode* n ){
    ROSE_ASSERT(n != NULL);

    ASTDeletionSupport::SafetyVisitor safetyChecker;
    safetyChecker.traverse(n,preorder); 
    ROSE_ASSERT(safetyChecker.isSafeToProceed());
    ASTDeletionSupport::DeleteAST deleteTree;
    deleteTree.traverse(n,postorder);
}
