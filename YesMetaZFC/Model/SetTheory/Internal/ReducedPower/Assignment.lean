import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Update

/-! # 从逐列代表函数读取商赋值

赋值族 V 的每列是一个实际 D→Q 函数，投影到对应等价类即得到商赋值。
列函数唯一，故整个构造使用 ZF 的唯一值收集，不需要选择代表元。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Rp_column_d (D V i f : M.Domain) : Prop := ∀ d, M.mem d D → ∀ v, M.PairMember I d v V →
  ∀ x, Rd_entry_d d x f ↔ M.PairMember I i x v

def rp_column_m {n} (D V i f : Term n) : Formula 1 n := Formula.forallMem D (.forallE
  (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest V.weaken.weaken) (.forallE
    (.iff (rd_entry0_m (.bound 2) .newest f.weaken.weaken.weaken)
      (Formula.orderedPairMem 𝒞 i.weaken.weaken.weaken .newest (.bound 1))))))
derive_free_closed rp_column_m

theorem rp_column_sat_l (hE : Extensional M) {n} (ρ : Env M n) (D V i f : Term n) :
    Formula.satisfies ρ (rp_column_m (𝒞 := 𝒞) D V i f) ↔
      Rp_column_d I (D.eval ρ) (V.eval ρ) (i.eval ρ) (f.eval ρ) := by
  simp only [rp_column_m, Rp_column_d, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_iff_iff,
    rd_entry0_sat_l hE, Definitional.Term.eval_weaken]
  rfl

theorem rp_column_exists_l (hZF : M.Models ZF) {ω D Q E V i} (hE : M.IsFunctionSpace I E ω Q)
    (hV : M.IsSetFunctionFromTo I V D E) (hi : M.mem i ω) : ∃ f, Fn0_d D Q f ∧ Rp_column_d I D V i f := by
  let ρ : Env M 2 := ⟨Fin.cases i (fun _ => V), fun _ => V⟩
  let φ : BinarySchema 2 := { body := .existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 4)) (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 1) .newest)) }
  have sat d x : φ.denote ρ d x ↔ ∃ v, M.PairMember I d v V ∧ M.PairMember I i x v := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_orderedPairMem_iff I]
    rfl
  obtain ⟨f, hf, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (kp_pair_l (ZF.modelsKP hZF)) φ ρ
    (source := D) (target := Q) (fun d hd => by
      obtain ⟨v, hv, hdv⟩ := hV.2.2 d hd
      obtain ⟨x, _, hix⟩ := ((hE v).mp hv).2.2 i hi
      exact ⟨x, (sat d x).mpr ⟨v, hdv, hix⟩⟩)
    (fun d _ x y hx hy => by
      obtain ⟨v, hdv, hix⟩ := (sat d x).mp hx
      obtain ⟨w, hdw, hiy⟩ := (sat d y).mp hy
      exact ((hE v).mp (hV.output_mem_of_pairMember hdv)).1.2 i x y hix (hV.1.2 d w v hdw hdv ▸ hiy))
    (fun d x _ hx => ((sat d x).mp hx).elim fun v hv =>
      ((hE v).mp (hV.output_mem_of_pairMember hv.1)).output_mem_of_pairMember hv.2)
  refine ⟨f, fn0_of_function_l (ZF.modelsKP hZF) hf, fun d hd v hv x => ?_⟩
  refine (show Rd_entry_d d x f ↔ M.mem d D ∧ φ.denote ρ d x from spec d x).trans ?_
  rw [sat d x]
  exact ⟨fun ⟨_, w, hw, hx⟩ => hV.1.2 d w v hw hv ▸ hx, fun hx => ⟨hd, v, hv, hx⟩⟩

theorem rp_column_unique_l (hE : Extensional M) {D Q E V i f g} (hV : M.IsSetFunctionFromTo I V D E)
    (hf : Fn0_d D Q f) (hg : Fn0_d D Q g) (hF : Rp_column_d I D V i f) (hG : Rp_column_d I D V i g) : f = g := by
  apply hf.ext_l hE hg
  intro d hd
  obtain ⟨v, _, hv⟩ := hV.2.2 d hd
  obtain ⟨x, _, hx⟩ := hf.2.1 d hd
  exact ⟨x, hx, (hG d hd v hv x).mpr ((hF d hd v hv x).mp hx)⟩

def Rp_eval_d (ω D p V e : M.Domain) : Prop := ∀ i, M.mem i ω → ∃ f B,
  M.PairMember I f B p ∧ M.PairMember I i B e ∧ Rp_column_d I D V i f

def rp_eval_m {n} (ω D p V e : Term n) : Formula 1 n := Formula.forallMem ω (.existsE (.existsE (.conj
  (Formula.orderedPairMem 𝒞 (.bound 1) .newest p.weaken.weaken.weaken) (.conj
    (Formula.orderedPairMem 𝒞 (.bound 2) .newest e.weaken.weaken.weaken)
    (rp_column_m (𝒞 := 𝒞) D.weaken.weaken.weaken V.weaken.weaken.weaken (.bound 2) (.bound 1))))))
derive_free_closed rp_eval_m

theorem rp_eval_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω D p V e : Term n) :
    Formula.satisfies ρ (rp_eval_m (𝒞 := 𝒞) ω D p V e) ↔
      Rp_eval_d I (ω.eval ρ) (D.eval ρ) (p.eval ρ) (V.eval ρ) (e.eval ρ) := by
  simp only [rp_eval_m, Rp_eval_d, Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_orderedPairMem_iff I, rp_column_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem rp_eval_exists_l (hZF : M.Models ZF) {ω D Q E U G p C V} (hp : Rp_map_d I D Q U G p C)
    (hG : ∀ f, Fn0_d D Q f → M.mem f G) (hE : M.IsFunctionSpace I E ω Q) (hV : M.IsSetFunctionFromTo I V D E) :
    ∃ e, M.IsSetFunctionFromTo I e ω C ∧ Rp_eval_d I ω D p V e := by
  let ρ : Env M 4 := ⟨Fin.cases V (Fin.cases D (Fin.cases p (fun _ => G))), fun _ => D⟩
  let φ : BinarySchema 4 := { body := Formula.existsMem (.bound 5) (.conj
    (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 5)) (rp_column_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) .newest)) }
  have sat i B : φ.denote ρ i B ↔ ∃ f, M.mem f G ∧ M.PairMember I f B p ∧ Rp_column_d I D V i f := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, rp_column_sat_l I hZF.1]
    rfl
  obtain ⟨e, he, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := C)
    (fun i hi => by
      obtain ⟨f, hf, hc⟩ := rp_column_exists_l I hZF hE hV hi
      obtain ⟨B, _, hb⟩ := hp.projection.2.2 f (hG f hf)
      exact ⟨B, (sat i B).mpr ⟨f, hG f hf, hb, hc⟩⟩)
    (fun i _ B A hB hA => by
      obtain ⟨f, hf, hfp, hF⟩ := (sat i B).mp hB
      obtain ⟨g, hg, hgp, hG⟩ := (sat i A).mp hA
      have eq := rp_column_unique_l I hZF.1 hV (hp.functions f hf) (hp.functions g hg) hF hG
      exact hp.projection.1.2 f B A hfp (eq.symm ▸ hgp))
    (fun i B _ hB => ((sat i B).mp hB).elim fun _ hf => hp.projection.output_mem_of_pairMember hf.2.1)
  refine ⟨e, he, fun i hi => ?_⟩
  obtain ⟨B, _, hb⟩ := he.2.2 i hi
  obtain ⟨f, _, hfp, hc⟩ := (sat i B).mp ((spec i B).mp hb).2
  exact ⟨f, B, hfp, hb, hc⟩

theorem Rp_eval_d.update_l {ω D Q E p V e i f B W e'} (h : Rp_eval_d I ω D p V e)
    (hf : Fn0_d D Q f) (hp : M.PairMember I f B p) (hW : Rp_update_d I D E V i f W)
    (he : Senv_update_d I e i B e') : Rp_eval_d I ω D p W e' := by
  intro j hj
  classical
  by_cases eq : j = i
  · subst j
    refine ⟨f, B, hp, (he.2 i B).mpr (Or.inl ⟨rfl, rfl⟩), fun d hd w hw x => ?_⟩
    obtain ⟨_, v, y, _, hy, hrow⟩ := (hW.2 d w).mp hw
    refine ⟨fun hx => (hrow.2 i x).mpr (Or.inl ⟨rfl, ?_⟩), fun hx => ?_⟩
    · exact hf.2.2 d hd x (hf.bound_l hx).2 y (hf.bound_l hy).2 hx hy
    · rcases (hrow.2 i x).mp hx with ⟨_, hxy⟩ | ⟨hn, _⟩
      · exact hxy.symm ▸ hy
      · exact (hn rfl).elim
  · obtain ⟨g, A, hgp, hje, hg⟩ := h j hj
    refine ⟨g, A, hgp, (he.2 j A).mpr (Or.inr ⟨eq, hje⟩), fun d hd w hw x => ?_⟩
    obtain ⟨_, v, _, hv, _, hrow⟩ := (hW.2 d w).mp hw
    exact (hg d hd v hv x).trans ⟨fun hx => (hrow.2 j x).mpr (Or.inr ⟨eq, hx⟩),
      fun hx => ((hrow.2 j x).mp hx).elim (fun he => (eq he.1).elim) And.right⟩

end YesMetaZFC.SetTheory.Internal
