  $ . ../setup-project.sh
  $ dune build test.vo
  *** [stmt1 := {s: $"foo" = !$"bar";} : Stmt]
  
  *** [expr1 := {e: (*&$"hello" + #3)} : Expr]
  
  *** [stmt2 :=
               {s: $"hello";
                   continue;
                   break;
                   $"world";
                   if ($"world") {
                     continue;
                   } else {
                     break;
                   }
                   // end block} : Stmt]
  
  *** [stmt3 :=
               {s: if (mut int32 $"x" = #0; $"x") {
                     continue;
                     continue;
                     continue;
                     continue;
                     // end block
                   } else {
                     break;
                   }
                   if (mut int32 $"x" = #0; $"x") {
                     // end block
                   } else {
                     break;
                   }
                   return $"x";
                   $"x";
                   return;
                   // end block} : Stmt]
  
  *** [stmt4 :=
               {s: if (mut int32 $"x" = #0; $"x") {
                     continue;
                   } else {
                     continue;
                     continue;
                     continue;
                     continue;
                     // end block
                   }
                   return $"x";
                   return;
                   // end block} : Stmt]
  
  *** [stmt5 :=
               {s: if (mut int32 $"x" = #0; $"x") {
                     continue;
                   } else {
                     continue;
                   }
                   return $"x";
                   return;
                   // end block} : Stmt]
  
  *** [stmt6 :=
               {s: if (mut int32 $"x" = #0; $"x") {
                     $"x"++;
                     // end block
                   } else {
                     continue;
                   }
                   // end block} : Stmt]
  
  *** [stmt7 :=
               {s: if (mut int32 $"x" = #0; $"x") {
                     $"x"++;
                     // end block
                   } else {
                     --$"x";
                     // end block
                   }
                   while (mut int32 $"x" = #0; $"x") {
                     $"x"--;
                     // end block
                   }
                   // end block} : Stmt]
  
  *** [stmt8 := {s: do {
                      $"x"--;
                      // end block
                    } while($"x");
                    // end block} : Stmt]
  
  *** [stmt9 :=
               {s: do {
                     $"foo" = !$"bar";
                     // end block
                   } while($"x");
                   // end block} : Stmt]
  
  *** [stmt10 :=
                {s: $"should_continue" =
                      !$::"_Z15process_commandPKN4Zeta8Zeta_ctxEPcR9UmxSharedRmR5Admin"(
                       $"ctx",
                       $"buffer",
                       $"shared",
                       $"client",
                       $"result");} : Stmt]
  
  *** [stmt11 :=
                {s: if (mut int32 $"x" = #0; $"x") {
                      continue;
                    } else {
                      continue;
                      continue;
                      continue;
                      continue;
                      // end block
                    }
                    return $"x";
                    return;
                    // end block} : Stmt]
  
  *** [stmt12 :=
                {s: if (mut int32 $"x" = #0; $"x") {
                      continue;
                    } else {
                      continue;
                    }
                    return $"x";
                    return;
                    // end block} : Stmt]
  
  *** [stmt13 :=
                {s: if (mut int32 $"x" = #0; $"x") {
                      $"x"++;
                      // end block
                    } else {
                      continue;
                    }
                    // end block} : Stmt]
  
  *** [stmt14 :=
                {s: if (mut int32 $"x" = #0; $"x") {
                      $"x"++;
                      // end block
                    } else {
                      --$"x";
                      // end block
                    }
                    while (mut int32 $"x" = #0; $"x") {
                      $"x"--;
                      // end block
                    }
                    // end block} : Stmt]
  
  *** [stmt15 := {s: do {
                       $"x"--;
                       // end block
                     } while($"x");
                     // end block} : Stmt]
  
  *** [stmt16 :=
                {s: do {
                      $"foo" = !$"bar";
                      // end block
                    } while($"x");
                    // end block} : Stmt]
  
  *** [stmt17 :=
                {s: $"should_continue" =
                      !$::"_Z15process_commandPKN4Zeta8Zeta_ctxEPcR9UmxSharedRmR5Admin"(
                       $"ctx",
                       $"buffer",
                       $"shared",
                       $"client",
                       $"result");} : Stmt]
  
