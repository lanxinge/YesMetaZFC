import YesMetaZFC.SetTheory.LargeCardinal.DerivedSeparation
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Restriction

/-! # 派生测度上的原嵌入求值

求值始终只对已经属于源的函数图定义。精确原子真值集的像在种子处读取，
从而同时识别商的等号及成员关系。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}}

def Ee_value_d (j a f y : M.Domain) : Prop := ∃ g, Rd_entry_d f g j ∧ Rd_entry_d a y g

def ee_value_m {d} (j a f y : Term d) : Formula 1 d := .existsE
  (.conj (rd_entry_m f.weaken .newest j.weaken) (rd_entry_m a.weaken y.weaken .newest))
derive_free_closed ee_value_m

theorem ee_value_sat_l (hE : Extensional M) {d} (ρ : Env M d) (j a f y : Term d) :
    Formula.satisfies ρ (ee_value_m j a f y) ↔ Ee_value_d (j.eval ρ) (a.eval ρ) (f.eval ρ) (y.eval ρ) := by
  simp only [ee_value_m, Ee_value_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem ed_evaluation_l (hZF : M.Models ZF) {ω X A Y B j D D' a f : M.Domain}
    (hω : M.IsOmega ω) (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X A Y B j)
    (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y) (hD : Rd_entry_d D D' j) (ha : M.mem a D')
    (hf : Sfun_d X D f) : ∃ y, M.mem y Y ∧ Ee_value_d j a f y ∧ ∀ z, Ee_value_d j a f z → z = y := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, e⟩ := h; exact e.1.1
  obtain ⟨hfX, C, hCX, hFC⟩ := hf
  obtain ⟨C', hCY, hjC⟩ := hj.2.2 C hCX
  obtain ⟨f', _, hjf⟩ := hj.2.2 f hfX
  have fun' := (spred_function_l I hZF hω h hX hY hD hjC hjf).mp hFC
  obtain ⟨y, hy, hay⟩ := fun'.2.1 a ha
  refine ⟨y, hY C' hCY y hy, ⟨f', hjf, hay⟩, fun z ⟨g, hjg, haz⟩ => ?_⟩
  have eq := hj.1.2 f g f' hjg hjf
  exact (fn0_function_l (ZF.modelsKP hZF) fun').1.2 a z y (eq ▸ haz) hay

theorem ed_evaluation_atoms_l (hZF : M.Models ZF) {ω X A Y B j D D' a U P c R f g y z : M.Domain}
    (hω : M.IsOmega ω) (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X A Y B j)
    (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y) (hD : Rd_entry_d D D' j) (ha : M.mem a D')
    (hP : M.IsPowerSetOf P D) (hPX : M.MemberSubset P X) (hU : Ed_filter_d (kp_pair_l (ZF.modelsKP hZF)) j a D U)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (hf : Sfun_d X D f) (hg : Sfun_d X D g) (hy : Ee_value_d j a f y) (hz : Ee_value_d j a g z) :
    (Rp_eq_d X U f g ↔ y = z) ∧ (Rp_rel_d (kp_pair_l (ZF.modelsKP hZF)) X U R f g ↔ M.mem y z) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, e⟩ := h; exact e.1.1
  obtain ⟨hfX, C, hCX, hFC⟩ := hf
  obtain ⟨hgX, E, hEX, hGE⟩ := hg
  obtain ⟨C', _, hjC⟩ := hj.2.2 C hCX
  obtain ⟨E', _, hjE⟩ := hj.2.2 E hEX
  obtain ⟨f', hjf, haf⟩ := hy
  obtain ⟨g', hjg, hag⟩ := hz
  have ff := (spred_function_l I hZF hω h hX hY hD hjC hjf).mp hFC
  have gg := (spred_function_l I hZF hω h hX hY hD hjE hjg).mp hGE
  have atom (b : Bool) :
      (∃ V, M.mem V U ∧ ∀ v, M.mem v V → Rp_atom_d I b X R f g v) ↔ (if b then y = z else M.mem y z) := by
    let φ : Delta0UnarySchema 4 := {
      body := Formula.existsMem (.bound 4) (Formula.existsMem (.bound 4)
        (.conj (rd_entry0_m (.bound 2) (.bound 1) (.bound 4)) (.conj (rd_entry0_m (.bound 2) .newest (.bound 3))
          (if b then Formula.extensionalEq (.bound 1) .newest else .mem (.bound 1) .newest))))
      freeClosed := by cases b <;> simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
      delta0 := .existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..)
        (by cases b; exact .mem _ _; exact .atom _ _ _)))) }
    let ρ := (((⟨fun _ => C, fun _ => C⟩ : Env M 1).push E).push f).push g
    let η := (((⟨fun _ => C', fun _ => C'⟩ : Env M 1).push E').push f').push g'
    have read (ρ : Env M 4) v : φ.toUnarySchema.denote ρ v ↔ ∃ x, M.mem x (ρ.bound 3) ∧ ∃ t, M.mem t (ρ.bound 2) ∧
        Rd_entry_d v x (ρ.bound 1) ∧ Rd_entry_d v t (ρ.bound 0) ∧ (if b then x = t else M.mem x t) := by
      cases b <;> simp only [φ, Bool.false_eq_true, ↓reduceIte, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
        rd_entry0_sat_l hZF.1, Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1] <;> rfl
    have source v : φ.toUnarySchema.denote ρ v ↔ Rp_atom_d I b X R f g v := by
      rw [read]
      constructor
      · rintro ⟨x, hx, t, ht, hfx, hgt, ht'⟩
        refine ⟨x, hX C hCX x hx, t, hX E hEX t ht, hfx, hgt, ?_⟩
        cases b
        · exact (hm.2 x t).mpr ⟨hX C hCX x hx, hX E hEX t ht, ht'⟩
        · exact ht'
      · rintro ⟨x, _, t, _, hfx, hgt, ht'⟩
        refine ⟨x, (hFC.bound_l hfx).2, t, (hGE.bound_l hgt).2, hfx, hgt, ?_⟩
        cases b
        · exact ((hm.2 x t).mp ht').2.2
        · exact ht'
    obtain ⟨V, hVX, vs, vu⟩ := ed_separate_delta_l I hZF hω h hX hY hP hPX hD ha hU φ ρ η
      (Fin.cases hjg (Fin.cases hjf (Fin.cases hjE (fun _ => hjC))))
    have target : φ.toUnarySchema.denote η a ↔ (if b then y = z else M.mem y z) := (read η a).trans
      ⟨fun ⟨x, _, t, _, hfx, hgt, ht⟩ =>
        (fn0_function_l (ZF.modelsKP hZF) ff).1.2 a x y hfx haf ▸
          (fn0_function_l (ZF.modelsKP hZF) gg).1.2 a t z hgt hag ▸ ht,
        fun ht => ⟨y, (ff.bound_l haf).2, z, (gg.bound_l hag).2, haf, hag, ht⟩⟩
    refine ⟨fun ⟨W, hw, truth⟩ => target.mp (vu.mp ?_), fun ht =>
      ⟨V, vu.mpr (target.mpr ht), fun v hv => (source v).mp ((vs v).mp hv).2⟩⟩
    obtain ⟨hWD, W', hjW, haW⟩ := (hU W).mp hw
    obtain ⟨V', _, hjV⟩ := hj.2.2 V hVX
    exact (hU V).mpr ⟨fun v hv => ((vs v).mp hv).1, V', hjV,
      (ed_subset_l I hZF hω h hX hY hjW hjV).mp
        (fun v hv => (vs v).mpr ⟨hWD v hv, (source v).mpr (truth v hv)⟩) a haW⟩
  exact ⟨(rp_atom_eq_l I (R := R)).symm.trans (atom true), atom false⟩

end YesMetaZFC.SetTheory.LargeCardinal
