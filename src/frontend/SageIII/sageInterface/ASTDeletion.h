#ifndef ROSE_SI_ASTDELETION
#define ROSE_SI_ASTDELETION
#include <iostream>
#include <cstdlib>
#include <vector>
#include <deque>
#include <map>
#include <utility>

namespace ASTDeletionSupport {

    //PRINT FUNCTIONS FOR DEBUGGING PURPOSES
    
    //printNode: Displays information about a given node.
    void printNode(SgNode* node);
    
    //printNodeExt: Extended print node function. Displays more information than the regular printNode function.
    void printNodeExt(SgNode* node);
    
    // FINDING SYMBOLS ASSOCIATED WITH NODES 
    // One of the most important parts of AST deletion is to identify symbols that are associated with
    // the nodes we want to delete, and to remove those symbols if and when they are no longer needed.
    // The following functions handle the process of finding the symbol associated with a node, if it
    // exists. The first function to be called is getAssociatedSymbol, which may delegate the task
    // to helper functions, namely handleDeclaration and handleExpression.
    
    //handleDeclaration: Attempts to retrieve a symbol associated with an SgDeclarationStatement node, if one exists.
    SgSymbol* handleDeclaration(SgDeclarationStatement* decl);
    
    //handleExpression: Attempts to retrieve a symbol associated with an SgExpression node, if one exists.
    SgSymbol* handleExpression(SgExpression* expr);
    
    //getAssociatedSymbol: Returns the symbol associated with this node, if one exists.
    SgSymbol* getAssociatedSymbol(SgNode* node);
    
    SgNode* reachProject(SgNode* node);
    
    //deleteSymbol: Removes the symbol from the table, and deallocates the symbol.
    void deleteSymbol(SgSymbolTable* table, SgSymbol* symbol);
    
    //deleteSymbol: Deallocates a type node.
    void deleteType(SgType* type);
    
    
    //CHECKING TO SEE WHETHER A SYMBOL CAN BE SAFELY DELETED
    // A symbol is safe to delete when only one node, the node we are going to delete next, is         
    // associated with it. To confirm this, we dispatch MemoryVisitor instances that traverse the      
    // memory pool in search of usages of a given symbol. It is assumed that we will find at least one 
    // node associated with the symbol, and that is the node for which we called getAssociatedSymbol.  
    // If we find any other usages of the symbol, then MemoryVisitor will report that it would be      
    // unsafe to delete it. A container is used to collect a list
    // of all the instances in which the symbol is used.        
    
    enum VisitorStatus {Unknown,Safe,Unsafe};
    typedef std::deque<SgNode*> NodeContainer;
    
    //MemoryVisitor: Visitor class that checks the memory pool for usages of a symbol.
    class MemoryVisitor : public ROSE_VisitorPattern {
        private:
        NodeContainer* matches; //A list of nodes whose associated symbol is the symbol passed to the MemoryVisitor.
        SgSymbol* symbol;
        void updateStatus();
        
        public:
        MemoryVisitor(SgSymbol* s);
        ~MemoryVisitor();
        
        //isSafeToDelete: After traversal, this function reports whether the given symbol is safe to delete.
        //If this function is called prematurely or if no matches were found during the traversal of the memory pool,
        //an assertion will fail.
        bool isSafeToDelete();
        
        //The visit function for the class.
        void visitDefault(SgNode* node);
        
        //getMatches: Returns the list of matches. This should be called only after the traversal is complete
        NodeContainer* getMatches();
    };
    
    class DeletionAnnotation : public AstAttribute {

    };
    
    
    //VERIFYING THAT A DELETION OPERATION IS SAFE
    // Choice. It's the best part of being a real person, but, if used incorrectly, can also be the
    // most dangerous. For example, deleting a node that is the basis for a symbol when that symbol
    // is used elsewhere is a terrible choice. SafetyVisitor exists to prevent the user from making
    // such choices. The class performs a pre-deletion traversal of the AST to confirm that the 
    // operation will not result in an AST that is invalid. If the deletion is safe to perform,
    // the SafetyVisitor will delete all symbols that will no longer be needed.
    
    //SafetyVisitor: Visitor class for the pre-deletion safety check traversal.
    class SafetyVisitor : public AstSimpleProcessing
    {
        private:
        bool safeToProceed; 
        std::multimap<SgSymbol*, SgNode*>* matchMap;
        NodeContainer* symbolList;
        
        public:
        SafetyVisitor();
        ~SafetyVisitor();
        bool isSafeToProceed();
        void visit (SgNode* node);
        void atTraversalEnd();
    };
    
    //DELETION
    // Below is the deletion routine proper, the heart of the deleteAST algorithm. The DeleteAST       
    // visitor traverses the selected subtree in post-order, cleanly deleting each node.               

    //DeleteAST: The is the visitor for the deletion traversal.
    class DeleteAST : public AstSimpleProcessing 
    {
        private:
        void clean(SgNode* node);
        public:
        void visit(SgNode* node);
    };


    class CleanupVisitor: public ROSE_VisitorPattern {
        private:
        NodeContainer* nodes;
        public:
        CleanupVisitor();
        ~CleanupVisitor();
        void visitDefault(SgNode* node);
        void finish();
    };


};

//DELETION ROUTINE
// Below is the deleteAST function called by the user. The algorithm is fairly straightforward.    
// First, a SafetyVisitor is deployed to the site of the deletion to confirm that the deletion can 
// proceed. Once the paperwork is completed, a DeleteAST visitor is employed to traverse the AST   
// and delete the targeted nodes.

namespace SageInterface {
    ROSE_DLL_API void deleteAST ( SgNode* n );
    ROSE_DLL_API void cleanMemoryPool();
};

#endif
