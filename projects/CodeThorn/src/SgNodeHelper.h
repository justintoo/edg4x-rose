#ifndef SgNodeHelper_H
#define SgNodeHelper_H

/*********************************
 * Author: Markus Schordan, 2012 *
 *********************************/

#include "rose.h"
#include <set>
#include <string>

using namespace std;

namespace SgNodeHelper {

  // returns the initializer expression of a variable declaration. If no initializer exists it returns 0.
  SgExpression* getInitializerExpressionOfVariableDeclaration(SgVariableDeclaration* decl);

  // returns the initialized name object of a variable declaration. Otherwise it throws an exception.
  SgInitializedName* getInitializedNameOfVariableDeclaration(SgVariableDeclaration* decl);

  /* computes for a given node at which scope nesting level this node is in its AST */
  int scopeNestingLevel(SgNode* node);

  // returns the root node representing the AST of the condition of If, While, DoWhile, For, CondOperator (does not handle switch).
  SgNode* getCond(SgNode* node);

  // returns the root node representing the AST of the true branch of If, CondOperator.
  SgNode* getTrueBranch(SgNode* node);

  // returns the root node representing the AST of the false branch of If, CondOperator.
  SgNode* getFalseBranch(SgNode* node);

  // returns the root node representing the AST of the loop body of While, DoWhile, For.
  SgNode* getLoopBody(SgNode* node);
  
  // returns the first Statement of SgBasicBlock (throws exception if numChildren==0)
  SgNode* getFirstOfBlock(SgNode* node);

  // returns the last Statement of SgBasicBlock (throws exception if numChildren==0)
  SgNode* getLastOfBlock(SgNode* node);

  // returns function name of SgFunctionDefinition and SgFunctionDeclaration
  string getFunctionName(SgNode* node);

  /* This is a lookup function currently not available in ROSE: It
	 determines for a given function-call-expression its corresponding
	 function-definition if available in the AST. There are three cases:

	 case 1: the associated declaration is a defining declaration. In
	 this case this directly referenced definition is returned
	 (available in ROSE).  

	 case 2: the associated declaration is a forward declaration. In
	 this case the entire AST is searched for the correct function
	 definition (this lookup is currently not available in
	 ROSE).

	 case 3: no definition is available.  (e.g. this is the case for
	 linked stdlib functions). In this case a null-pointer is
	 returned. This can only be determined after case 2 has been
	 checked.
  */
  SgFunctionDefinition* determineFunctionDefinition(SgFunctionCallExp* fCall);

  bool isForwardFunctionDeclaration(SgNode* declaration);  

  /* this function should only be called for a node in the subtree of
	 a SgFunctionDefinition node. For a given 'node' it determines the
	 correspondnig functionDefinition node when searching upwards
	 in the AST for such a SgFunctionDefinition node. It is useful as a
	 simple lookup function from inside the AST subtree of a
	 SgFunctionDefinition.  Returns 0 if no SgFunctionDefinition is found (e.g. global scope).
  */
  SgFunctionDefinition* correspondingSgFunctionDefinition(SgNode* node);

  // checks whether the node 'node' is the root node of the AST by using the get_parent function.
  bool isAstRoot(SgNode* node);

  // is true if 'node' is the root node of the AST representing the condition of If, While, DoWhile, For. (does not handle switch).
  bool isCond(SgNode* node);

  // returns a SgSymbol* for a variale in a variable declaration
  SgSymbol* getSymbolOfVariableDeclaration(SgVariableDeclaration* decl);

  // returns a SgSymbol* for a variable in a SgVarRefExp
  SgSymbol* getSymbolOfVariable(SgVarRefExp* decl);

  // returns name of symbol as string
  string symbolToString(SgSymbol* symbol);

  /* Creates a long unique variable name for a given node of type SgVariableDeclaration or SgVarRefExp
	 If node is not one of those two types an exception is thrown
	 The long variable name consists $functionName$scopeLevel$varName
	 In case of global scope functionName is empty, giving a string: $$scopeLevel$varName 
	 Note: this function only considers C-functions. Classes are recognized.
  */
  string uniqueLongVariableName(SgNode* node);

  /* returns a set of SgNode where each node is a break node, but
	 properly excludes all nested loops. Hence, the parameter 'node' can
	 point directly to the AST construct (e.g. SgIfStatement) or a basic
	 block of the respective loop construct. It is quit flexible, the only property
	 it maintains is that it does not collect break nodes from nested loops
	 but only from the current scope. 
	 This function can be used for SgWhile,SgDoWhile,SgForStatement, SgSwitch.
  */
  set<SgNode*> LoopRelevantBreakStmtNodes(SgNode* node);

  // returns the first child of an arbitrary AST node (throws exception if numChildren==0)
  SgNode* getFirstChild(SgNode* node);

  // return a function-call's list of actual parameters
  SgExpressionPtrList& getFunctionCallActualParameterList(SgNode* node);

  // return a function-definition's list of formal paramters
  SgInitializedNamePtrList& getFunctionDefinitionFormalParameterList(SgNode* node);

  // returns the child of SgExprStatement (which is guaranteed to be unique and to exist)
  SgNode* getExprStmtChild(SgNode* node);

  // returns the child of SgExpressionRoot (which is guaranteed to be unique and to exist)
  SgNode* getExprRootChild(SgNode* node);

  /* returns the number of children as int (intentionally not as t_size)
	 ensures that the number of children fits into an int, otherwise throws exception.
  */
  int numChildren(SgNode* node);

  // computes a new string from s1 where each doublequote '"' is replaced with \". This is helpful when printing
  // unparsed program fragments which contain doublequoted strings to a dot file (used by nodeToString).
  string doubleQuotedEscapedString(string s1);

  // returns a string representing the node (excluding the subtree)
  string nodeToString(SgNode* node);

  // return lhs of a binary node (if it is not a binary node it throws an exception)
  SgNode* getLhs(SgNode* node);

  // return rhs of a binary node (if it is not a binary node it throws an exception)
  SgNode* getRhs(SgNode* node);
  
  /* returns the parent of a node. Essentially a wrapper function of the ROSE get_parent() function, but throws
	 an expection if no parent exists. 
  */
  SgNode* getParent(SgNode* node);

  /* searches in the provided Project for SgGlobal nodes */
  list<SgGlobal*> listOfSgGlobal(SgProject* project);

  /* identifies the list of global variables
	 Note: static/external can be resolved by further processing those objects
   */
  list<SgVariableDeclaration*> listOfGlobalVars(SgProject* project);
  /* identifies the list of global variables
	 Note: static/external can be resolved by further processing those objects
   */
  list<SgVariableDeclaration*> listOfGlobalVars(SgGlobal* global);

  /* identifies the list of SgFunctionDefinitions in global scope
     Functions/methods of classes are NOT included in this list.
	 Note: static/external can be resolved by further processing those objects
  */
  list<SgFunctionDefinition*> listOfGlobalFunctionDefinitions(SgGlobal* global);


  namespace Pattern {
	// tests several patterns and returns pointer to FunctionCallExp inside that matched pattern, otherwise 0.
	SgFunctionCallExp* matchFunctionCall(SgNode *);
	// tests pattern SgReturnStmt(FunctionCallExp) and returns pointer to FunctionCallExp, otherwise 0.
	SgFunctionCallExp* matchReturnStmtFunctionCallExp(SgNode *);
	// tests pattern SgExprStatement(FunctionCallExp) and returns pointer to FunctionCallExp, otherwise 0.
	SgFunctionCallExp* matchExprStmtFunctionCallExp(SgNode *);
	// tests pattern SgExprStatement(SgAssignOp(VarRefExp,FunctionCallExp)) and returns pointer to FunctionCallExp, otherwise 0.
	SgFunctionCallExp* matchExprStmtAssignOpVarRefExpFunctionCallExp(SgNode *);
  } // end of namespace Pattern

} // end of namespace SgNodeHelper

#endif
