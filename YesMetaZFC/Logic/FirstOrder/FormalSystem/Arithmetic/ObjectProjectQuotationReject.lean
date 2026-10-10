import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectProjectQuotationAccept

/-! # quotation 转换对任意自然数输出的拒绝证书 -/
namespace YesMetaZFC.Automation.ObjectProjectQuotation
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem ProofT NatPacket IntrinsicQuotation ProofCode
open ObjectHorn
set_option autoImplicit false

private theorem unary_result (tag : Nat) (body : Tree) (out : Nat)
    (hTag : tag = 4 ∨ tag = 9 ∨ tag = 10) (hBody : (run body).map treeValue = some out) :
    (run (.node tag [body])).map treeValue = some (nodeValue tag [out]) := by
  obtain ⟨decoded, hRun, rfl⟩ := Option.map_eq_some_iff.mp hBody
  rcases hTag with rfl | rfl | rfl
  all_goals rw [run.eq_def]; simp [hRun]

private theorem binary_result (tag : Nat) (left right : Tree) (a b : Nat)
    (hTag : tag = 5 ∨ tag = 6 ∨ tag = 7 ∨ tag = 8)
    (hLeft : (run left).map treeValue = some a) (hRight : (run right).map treeValue = some b) :
    (run (.node tag [left, right])).map treeValue = some (nodeValue tag [a, b]) := by
  obtain ⟨decodedLeft, hLeftRun, rfl⟩ := Option.map_eq_some_iff.mp hLeft
  obtain ⟨decodedRight, hRightRun, rfl⟩ := Option.map_eq_some_iff.mp hRight
  rcases hTag with rfl | rfl | rfl | rfl
  all_goals rw [run.eq_def]; simp [hLeftRun, hRightRun]

private theorem unary_matched (tag : Nat) (input : Tree) (output : Nat) (values : Fin 2 → Nat)
    (hTag : tag = 4 ∨ tag = 9 ∨ tag = 10)
    (hHead : row input output = nodeValue 0 [nodeValue tag [values 0] , nodeValue tag [values 1]])
    (hBad : (run input).map treeValue ≠ some output)
    (ih : ∀ child out, sizeOf child < sizeOf input → (run child).map treeValue ≠ some out →
      Rejection rules (row child out)) :
    ∃ premise, premise ∈ (unaryRule tag).premises ∧ Rejection rules (premise.eval values) := by
  have h := ((nodeValue_eq_iff 0 0 [treeValue input, output]
    [nodeValue tag [values 0] , nodeValue tag [values 1]]).mp hHead).2
  simp only [List.cons.injEq, and_true] at h
  obtain ⟨body, rfl, hBody⟩ := treeValue_node_one h.1
  refine ⟨node (n := 2) 0 [.var 0, .var 1] , List.mem_cons_self, ?_⟩
  change Rejection rules (nodeValue 0 [values 0, values 1])
  rw [← hBody]
  apply ih body (values 1) (by simp; omega)
  intro hRun
  apply hBad
  rw [h.2]
  exact unary_result tag body _ hTag hRun

private theorem binary_matched (tag : Nat) (input : Tree) (output : Nat) (values : Fin 4 → Nat)
    (hTag : tag = 5 ∨ tag = 6 ∨ tag = 7 ∨ tag = 8)
    (hHead : row input output = nodeValue 0
      [nodeValue tag [values 0, values 1] , nodeValue tag [values 2, values 3]])
    (hBad : (run input).map treeValue ≠ some output)
    (ih : ∀ child out, sizeOf child < sizeOf input → (run child).map treeValue ≠ some out →
      Rejection rules (row child out)) :
    ∃ premise, premise ∈ (binaryRule tag).premises ∧ Rejection rules (premise.eval values) := by
  classical
  have h := ((nodeValue_eq_iff 0 0 [treeValue input, output]
    [nodeValue tag [values 0, values 1] , nodeValue tag [values 2, values 3]]).mp hHead).2
  simp only [List.cons.injEq, and_true] at h
  obtain ⟨left, right, rfl, hLeft, hRight⟩ := treeValue_node_two h.1
  by_cases hRunLeft : (run left).map treeValue = some (values 2)
  · refine ⟨node (n := 4) 0 [.var 1, .var 3] , List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    change Rejection rules (nodeValue 0 [values 1, values 3])
    rw [← hRight]
    apply ih right (values 3) (by simp; omega)
    intro hRunRight
    apply hBad
    rw [h.2]
    exact binary_result tag left right _ _ hTag hRunLeft hRunRight
  · refine ⟨node (n := 4) 0 [.var 0, .var 2] , List.mem_cons_self, ?_⟩
    change Rejection rules (nodeValue 0 [values 0, values 2])
    rw [← hLeft]
    exact ih left _ (by simp; omega) hRunLeft

private theorem atom_matched (tag : Nat) (input : Tree) (output : Nat) (values : Fin 1 → Nat)
    (hTag : tag = 2 ∨ tag = 3 ∨ tag = 11)
    (hHead : row input output = (atomRule tag).head.eval values) :
    (run input).map treeValue = some output := by
  have h := ((nodeValue_eq_iff 0 0 [treeValue input, output]
    [godel_pair_value tag (values 0) + 1, (atomExpr tag (.var (0 : Fin 1))).eval values]).mp hHead).2
  simp only [List.cons.injEq, and_true] at h
  cases input with
  | node actual children =>
    have hCode := h.1
    rw [treeValue_node] at hCode
    have hData := godel_pair_value_eq_iff.mp (Nat.add_right_cancel hCode)
    rcases hData with ⟨rfl, hFields⟩
    have hOut : treeValue (atom actual children) = output := by
      rw [atom_value, h.2]
      congr 1
      funext i
      have hi : i = 0 := by apply Fin.ext; omega
      subst i
      exact hFields
    rcases hTag with rfl | rfl | rfl
    all_goals rw [run.eq_def]; exact congrArg some hOut

theorem run_reject (input : Tree) (output : Nat) (hBad : (run input).map treeValue ≠ some output) :
    Rejection rules (row input output) := by
  apply Rejection.of_tagged heads_tagged 0 [treeValue input, output]
  intro rule hRule values _ hHead _
  have ih : ∀ child out, sizeOf child < sizeOf input → (run child).map treeValue ≠ some out →
      Rejection rules (row child out) := by
    intro child out _ hChild
    exact run_reject child out hChild
  rw [rulesFor_zero] at hRule
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hRule
  rcases hRule with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only [constantRule, atomRule, unaryRule, binaryRule] at values hHead ⊢
  · have h := ((nodeValue_eq_iff 0 0 [treeValue input, output]
      [nodeValue 0 [] , nodeValue 0 []]).mp hHead).2
    simp only [List.cons.injEq, and_true] at h
    exact False.elim (hBad (by rw [treeValue_node_zero h.1, h.2, run.eq_def]; rfl))
  · have h := ((nodeValue_eq_iff 0 0 [treeValue input, output]
      [nodeValue 1 [] , nodeValue 1 []]).mp hHead).2
    simp only [List.cons.injEq, and_true] at h
    exact False.elim (hBad (by rw [treeValue_node_zero h.1, h.2, run.eq_def]; rfl))
  · exact False.elim (hBad (atom_matched 2 input output values (by simp) hHead))
  · exact False.elim (hBad (atom_matched 3 input output values (by simp) hHead))
  · exact unary_matched 4 input output values (by simp) hHead hBad ih
  · exact binary_matched 5 input output values (by simp) hHead hBad ih
  · exact binary_matched 6 input output values (by simp) hHead hBad ih
  · exact binary_matched 7 input output values (by simp) hHead hBad ih
  · exact binary_matched 8 input output values (by simp) hHead hBad ih
  · exact unary_matched 9 input output values (by simp) hHead hBad ih
  · exact unary_matched 10 input output values (by simp) hHead hBad ih
  · exact False.elim (hBad (atom_matched 11 input output values (by simp) hHead))
termination_by sizeOf input

end YesMetaZFC.Automation.ObjectProjectQuotation
