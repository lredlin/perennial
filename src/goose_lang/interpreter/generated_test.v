(* autogenerated by goose/cmd/test_gen *)
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.
From Perennial.goose_lang.interpreter Require Import test_config.

(* test functions *)
From Goose.github_com.goose_lang.goose.internal.examples Require Import semantics.

(* allocator.go *)
Example testAllocateDistinct_ok : testAllocateDistinct #() ~~> #true := t.
Example testAllocateFull_ok : testAllocateFull #() ~~> #true := t.

(* append.go *)
Example testSingleAppend_ok : testSingleAppend #() ~~> #true := t.
Example testAppendToCapacity_ok : testAppendToCapacity #() ~~> #true := t.
Example testAppendSlice_ok : testAppendSlice #() ~~> #true := t.

(* assign_ops.go *)
Example testAssignAddSub_ok : testAssignAddSub #() ~~> #true := t.
Example testAssignBitwise_ok : testAssignBitwise #() ~~> #true := t.

(* atomic.go *)
Example testAtomicLoadStore64_ok : testAtomicLoadStore64 #() ~~> #true := t.
Example testAtomicPointers_ok : testAtomicPointers #() ~~> #true := t.

(* closures.go *)
Example testClosureBasic_ok : testClosureBasic #() ~~> #true := t.

(* comparisons.go *)
Example testCompareAll_ok : testCompareAll #() ~~> #true := t.
Example testCompareGT_ok : testCompareGT #() ~~> #true := t.
Example testCompareGE_ok : testCompareGE #() ~~> #true := t.
Example testCompareLT_ok : testCompareLT #() ~~> #true := t.
Example testCompareLE_ok : testCompareLE #() ~~> #true := t.

(* conversions.go *)
Example testByteSliceToString_ok : testByteSliceToString #() ~~> #true := t.
Example testStringToByteSliceAlias_ok : testStringToByteSliceAlias #() ~~> #true := t.

(* copy.go *)
Example testCopySimple_ok : testCopySimple #() ~~> #true := t.
Example testCopyShorterDst_ok : testCopyShorterDst #() ~~> #true := t.
Example testCopyShorterSrc_ok : testCopyShorterSrc #() ~~> #true := t.

(* encoding.go *)
Example testEncDec32Simple_ok : testEncDec32Simple #() ~~> #true := t.
Fail Example testEncDec32_ok : failing_testEncDec32 #() ~~> #true := t.
Example testEncDec64Simple_ok : testEncDec64Simple #() ~~> #true := t.
Example testEncDec64_ok : testEncDec64 #() ~~> #true := t.

(* first_class_function.go *)
Example testFirstClassFunction_ok : testFirstClassFunction #() ~~> #true := t.

(* function_ordering.go *)
Fail Example testFunctionOrdering_ok : failing_testFunctionOrdering #() ~~> #true := t.
Fail Example testArgumentOrder_ok : failing_testArgumentOrder #() ~~> #true := t.

(* generics.go *)
Example testGenerics_ok : testGenerics #() ~~> #true := t.

(* int_conversions.go *)
Example testU64ToU32_ok : testU64ToU32 #() ~~> #true := t.
Example testU32Len_ok : testU32Len #() ~~> #true := t.
Fail Example testU32NewtypeLen_ok : failing_testU32NewtypeLen #() ~~> #true := t.

(* interfaces.go *)
Example testBasicInterface_ok : testBasicInterface #() ~~> #true := t.
Example testAssignInterface_ok : testAssignInterface #() ~~> #true := t.
Example testMultipleInterface_ok : testMultipleInterface #() ~~> #true := t.
Example testBinaryExprInterface_ok : testBinaryExprInterface #() ~~> #true := t.
Example testIfStmtInterface_ok : testIfStmtInterface #() ~~> #true := t.

(* interfaces_failing.go *)

(* lock.go *)
Example testsUseLocks_ok : testsUseLocks #() ~~> #true := t.

(* loops.go *)
Example testStandardForLoop_ok : testStandardForLoop #() ~~> #true := t.
Example testForLoopWait_ok : testForLoopWait #() ~~> #true := t.
Example testBreakFromLoopWithContinue_ok : testBreakFromLoopWithContinue #() ~~> #true := t.
Example testBreakFromLoopNoContinue_ok : testBreakFromLoopNoContinue #() ~~> #true := t.
Example testBreakFromLoopNoContinueDouble_ok : testBreakFromLoopNoContinueDouble #() ~~> #true := t.
Example testBreakFromLoopForOnly_ok : testBreakFromLoopForOnly #() ~~> #true := t.
Example testBreakFromLoopAssignAndContinue_ok : testBreakFromLoopAssignAndContinue #() ~~> #true := t.
Example testNestedLoops_ok : testNestedLoops #() ~~> #true := t.
Example testNestedGoStyleLoops_ok : testNestedGoStyleLoops #() ~~> #true := t.
Example testNestedGoStyleLoopsNoComparison_ok : testNestedGoStyleLoopsNoComparison #() ~~> #true := t.

(* maps.go *)
Example testIterateMap_ok : testIterateMap #() ~~> #true := t.
Example testMapSize_ok : testMapSize #() ~~> #true := t.

(* multiple_assign.go *)
Example testAssignTwo_ok : testAssignTwo #() ~~> #true := t.
Example testAssignThree_ok : testAssignThree #() ~~> #true := t.
Example testMultipleAssignToMap_ok : testMultipleAssignToMap #() ~~> #true := t.

(* multiple_return.go *)
Example testReturnTwo_ok : testReturnTwo #() ~~> #true := t.
Example testAnonymousBinding_ok : testAnonymousBinding #() ~~> #true := t.
Example testReturnThree_ok : testReturnThree #() ~~> #true := t.
Example testReturnFour_ok : testReturnFour #() ~~> #true := t.

(* nil.go *)
Fail Example testCompareSliceToNil_ok : failing_testCompareSliceToNil #() ~~> #true := t.
Example testComparePointerToNil_ok : testComparePointerToNil #() ~~> #true := t.
Example testCompareNilToNil_ok : testCompareNilToNil #() ~~> #true := t.
Example testComparePointerWrappedToNil_ok : testComparePointerWrappedToNil #() ~~> #true := t.
Example testComparePointerWrappedDefaultToNil_ok : testComparePointerWrappedDefaultToNil #() ~~> #true := t.

(* operations.go *)
Example testReverseAssignOps64_ok : testReverseAssignOps64 #() ~~> #true := t.
Fail Example testReverseAssignOps32_ok : failing_testReverseAssignOps32 #() ~~> #true := t.
Example testAdd64Equals_ok : testAdd64Equals #() ~~> #true := t.
Example testSub64Equals_ok : testSub64Equals #() ~~> #true := t.
Example testDivisionPrecedence_ok : testDivisionPrecedence #() ~~> #true := t.
Example testModPrecedence_ok : testModPrecedence #() ~~> #true := t.
Example testBitwiseOpsPrecedence_ok : testBitwiseOpsPrecedence #() ~~> #true := t.
Example testArithmeticShifts_ok : testArithmeticShifts #() ~~> #true := t.
Example testBitAddAnd_ok : testBitAddAnd #() ~~> #true := t.
Example testManyParentheses_ok : testManyParentheses #() ~~> #true := t.
Example testPlusTimes_ok : testPlusTimes #() ~~> #true := t.

(* precedence.go *)
Example testOrCompareSimple_ok : testOrCompareSimple #() ~~> #true := t.
Example testOrCompare_ok : testOrCompare #() ~~> #true := t.
Example testAndCompare_ok : testAndCompare #() ~~> #true := t.
Example testShiftMod_ok : testShiftMod #() ~~> #true := t.

(* prims.go *)
Example testLinearize_ok : testLinearize #() ~~> #true := t.

(* shortcircuiting.go *)
Example testShortcircuitAndTF_ok : testShortcircuitAndTF #() ~~> #true := t.
Example testShortcircuitAndFT_ok : testShortcircuitAndFT #() ~~> #true := t.
Example testShortcircuitOrTF_ok : testShortcircuitOrTF #() ~~> #true := t.
Example testShortcircuitOrFT_ok : testShortcircuitOrFT #() ~~> #true := t.

(* slices.go *)
Example testSliceOps_ok : testSliceOps #() ~~> #true := t.
Example testSliceCapacityOps_ok : testSliceCapacityOps #() ~~> #true := t.
Example testOverwriteArray_ok : testOverwriteArray #() ~~> #true := t.

(* strings.go *)
Fail Example testStringAppend_ok : failing_testStringAppend #() ~~> #true := t.
Fail Example testStringLength_ok : failing_testStringLength #() ~~> #true := t.

(* struct_pointers.go *)
Fail Example testFooBarMutation_ok : failing_testFooBarMutation #() ~~> #true := t.

(* structs.go *)
Fail Example testStructUpdates_ok : failing_testStructUpdates #() ~~> #true := t.
Example testNestedStructUpdates_ok : testNestedStructUpdates #() ~~> #true := t.
Example testStructConstructions_ok : testStructConstructions #() ~~> #true := t.
Example testIncompleteStruct_ok : testIncompleteStruct #() ~~> #true := t.
Example testStoreInStructVar_ok : testStoreInStructVar #() ~~> #true := t.
Example testStoreInStructPointerVar_ok : testStoreInStructPointerVar #() ~~> #true := t.
Example testStoreComposite_ok : testStoreComposite #() ~~> #true := t.
Example testStoreSlice_ok : testStoreSlice #() ~~> #true := t.
Example testStructFieldFunc_ok : testStructFieldFunc #() ~~> #true := t.

(* vars.go *)
Example testPointerAssignment_ok : testPointerAssignment #() ~~> #true := t.
Example testAddressOfLocal_ok : testAddressOfLocal #() ~~> #true := t.
Example testAnonymousAssign_ok : testAnonymousAssign #() ~~> #true := t.

(* wal.go *)

