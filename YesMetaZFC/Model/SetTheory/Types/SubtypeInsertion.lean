import YesMetaZFC.Model.SetTheory.Types.SubtypeWitness
import YesMetaZFC.Model.SetTheory.Types.Embedding
import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding

/-! # 在高度坐标前插入新标签的实际子类型见证

旧元组末位移至新末位，新标签占据旧末位。交换这两个位置的内部排列图和
全赋值图均在 ZF 中构造；旧前缀长度不要求外部标准。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

theorem ts_at_insert_l {ω ν A c R l n m r s δ U D w β x : M.Domain}
    (hω : M.IsOmega ω) (hn : M.SuccessorOf n l) (hm : M.SuccessorOf m n)
    (hA : V_d I ν A) (model : Smem_d I c A R) (type : Tt_realized_d I ω c A R m s δ U D w)
    (old : Tg_graph_d I n r) (kept : ∀ i y, M.mem i l → (Rd_entry_d i y r ↔ Rd_entry_d i y s))
    (last : Rd_entry_d l β r) (inserted : Rd_entry_d l x s) (moved : Rd_entry_d n β s) :
    Ts_at_d hZF ω δ n r m U D w ν := by
  classical
  have om := hω.members_areOrdinals (ZF.modelsKP hZF) m type.finite
  have on := om.mem hm.predecessor_mem
  have lm := om.transitive n hm.predecessor_mem l hn.predecessor_mem
  have ne : l ≠ n := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) n (eq ▸ hn.predecessor_mem)
  have cases i (hi : M.mem i m) : M.mem i l ∨ i = l ∨ i = n := by
    rcases (hm i).mp hi with hi | eq
    · exact ((hn i).mp hi).elim Or.inl (fun eq => Or.inr (Or.inl (hZF.1.eq_of_same_members i l eq)))
    · exact Or.inr (Or.inr (hZF.1.eq_of_same_members i n eq))
  let f (i : M.Domain) := if i = l then n else if i = n then l else i
  have inv i : f (f i) = i := by
    by_cases hi : i = l
    · subst i; simp [f, ne.symm]
    · by_cases hj : i = n
      · subst i; simp [f, ne.symm]
      · simp only [f, if_neg hi, if_neg hj]
  have fm i (hi : M.mem i m) : M.mem (f i) m := by
    by_cases hl : i = l
    · simp only [f, if_pos hl]; exact hm.predecessor_mem
    · by_cases hn : i = n
      · simp only [f, if_neg hl, if_pos hn]; exact lm
      · simpa only [f, if_neg hl, if_neg hn] using hi
  let ρ : Env M 2 := ⟨Fin.cases l (fun _ => n), fun _ => n⟩
  let φ : BinarySchema 2 := { body := set[4] ⟪
    (⌜(.bound 1 : Term 4)⌝ₛ = ⌜(.bound 2 : Term 4)⌝ₛ ∧ ⌜(.bound 0 : Term 4)⌝ₛ = ⌜(.bound 3 : Term 4)⌝ₛ) ∨
    (¬ (⌜(.bound 1 : Term 4)⌝ₛ = ⌜(.bound 2 : Term 4)⌝ₛ) ∧
      ((⌜(.bound 1 : Term 4)⌝ₛ = ⌜(.bound 3 : Term 4)⌝ₛ ∧ ⌜(.bound 0 : Term 4)⌝ₛ = ⌜(.bound 2 : Term 4)⌝ₛ) ∨
       (¬ (⌜(.bound 1 : Term 4)⌝ₛ = ⌜(.bound 3 : Term 4)⌝ₛ) ∧ ⌜(.bound 0 : Term 4)⌝ₛ = ⌜(.bound 1 : Term 4)⌝ₛ)))⟫ }
  have sat i j : φ.denote ρ i j ↔ j = f i := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1]
    change ((i = l ∧ j = n) ∨ (i ≠ l ∧ ((i = n ∧ j = l) ∨ (i ≠ n ∧ j = i)))) ↔ j = f i
    by_cases hl : i = l
    · simp [hl, f]
    · by_cases hn : i = n <;> simp [f, hl, hn, ne.symm]
  obtain ⟨π, fp, entries⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := m) (target := m)
    (fun i _ => ⟨f i, (sat i (f i)).mpr rfl⟩)
    (fun i _ x y hx hy => ((sat i x).mp hx).trans ((sat i y).mp hy).symm)
    (fun i j hi hj => ((sat i j).mp hj).symm ▸ fm i hi)
  have pe i j : Rd_entry_d i j π ↔ M.mem i m ∧ j = f i := (entries i j).trans (and_congr_right fun _ => sat i j)
  have bij : M.IsSetBijectionFromTo I π m m := ⟨⟨fp, fun i j y hi hj =>
    (inv i).symm.trans ((congrArg f (((pe i y).mp hi).2.symm.trans ((pe j y).mp hj).2)).trans (inv j))⟩,
    fun y hy => ⟨f y, fm y hy, (pe (f y) y).mpr ⟨fm y hy, (inv y).symm⟩⟩⟩
  have fr : M.IsSetFunctionFromTo I r n A := ⟨old.1, old.2, fun i hi => by
    obtain ⟨y, hy⟩ := (old.2 i).mp hi
    refine ⟨y, ?_, hy⟩
    rcases (hn i).mp hi with hi | eq
    · exact (type.tuple.bound_l ((kept i y hi).mp hy)).2
    · exact (old.1.2 l y β (hZF.1.eq_of_same_members i l eq ▸ hy) last).symm ▸ (type.tuple.bound_l moved).2⟩
  obtain ⟨t, ft, tk, tx⟩ := tt_column_append_l hZF on hm fr (type.tuple.bound_l inserted).2
  obtain ⟨a, fill, fa⟩ := senv_fill_exists_l I hZF ft type.point
  obtain ⟨g, fg, recode⟩ := fn_recode_l I K hZF fa
  obtain ⟨h, fh, graph⟩ := fn_recode_l I K hZF (fn0_function_l (ZF.modelsKP hZF) type.tuple)
  have atT i y (hi : M.mem i m) : Rd_entry_d i y t ↔ M.PairMember K i y g := by
    rw [recode i y]
    exact ⟨fun hx => (fill.2 i y).mpr ⟨hω.transitive (ZF.modelsKP hZF) m type.finite i hi, Or.inl ⟨hi, hx⟩⟩,
      fun hx => ((fill.2 i y).mp hx).2.elim And.right (fun h => (h.1 hi).elim)⟩
  have orig i y (hi : M.mem i n) : Rd_entry_d i y r ↔ M.PairMember K i y g :=
    (tk i y hi).symm.trans (atT i y (om.transitive n hm.predecessor_mem i hi))
  have matchValue i y (hi : M.mem i m) (hy : Rd_entry_d i y s) : M.PairMember K (f i) y g := by
    rcases cases i hi with hi | eqi | eqi
    · have il : i ≠ l := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) l (eq ▸ hi)
      have inn : i ≠ n := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) n
        (eq ▸ on.transitive l hn.predecessor_mem i hi)
      simpa only [f, if_neg il, if_neg inn] using
        (orig i y (on.transitive l hn.predecessor_mem i hi)).mp ((kept i y hi).mpr hy)
    · subst i
      have eq := (fn0_function_l (ZF.modelsKP hZF) type.tuple).1.2 l y x hy inserted
      simpa [f] using (eq.symm ▸ (atT n x hm.predecessor_mem).mp tx)
    · subst i
      have eq := (fn0_function_l (ZF.modelsKP hZF) type.tuple).1.2 n y β hy moved
      simpa [f, ne.symm] using (eq.symm ▸ (orig l β hn.predecessor_mem).mp last)
  refine ⟨A, c, R, s, g, h, π, hA, model, type, fg, fh, graph, orig, bij, fun i hi y _ => ?_⟩
  constructor
  · intro hy
    exact ⟨f i, fm i hi, (pe i (f i)).mpr ⟨hi, rfl⟩, matchValue i y hi ((graph i y).mp hy)⟩
  · rintro ⟨j, _, ij, jy⟩
    obtain ⟨x, _, ix⟩ := type.tuple.2.1 i hi
    have eq := fg.1.2 (f i) y x (((pe i j).mp ij).2 ▸ jy) (matchValue i x hi ix)
    exact (graph i y).mpr (eq.symm ▸ ix)

end YesMetaZFC.SetTheory.Internal
