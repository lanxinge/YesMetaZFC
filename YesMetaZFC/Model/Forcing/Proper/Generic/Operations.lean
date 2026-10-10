import YesMetaZFC.Model.Forcing.Proper.Generic.Rule
import YesMetaZFC.SetTheory.Card.FiniteSequenceEnd
import YesMetaZFC.SetTheory.FinitaryClub

/-! # 统一判定与见证选择的实际有限元运算

第一张图输出稠密判定集，第二张图读取参数列的末项条件并选择 X 中的名称见证。
无见证时第二张图返回既定基点。两张图都由原集合论公理实际构造，随后可在任意
proper club 中同时闭包，不预设小模型对力迫满足关系的封闭性。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Ng_dense_op_d {n} (φ : UnarySchema (n+3)) (ρ : Env M n) (B R z b X k D : M.Domain) : Prop :=
  ∃ l f, KPair_d M k l f ∧ Ng_rule_decide_d φ ρ B R z b X l f D

def ng_dense_op_m {n d} (φ : UnarySchema (n+3)) (e : Fin n → Term d)
    (B R z b X k D : Term d) : Formula 1 d :=
  .existsE (.existsE (.conj (kpair_m k.weaken.weaken (.bound 1) .newest)
    (ng_rule_decide_m φ (fun i => (e i).weaken.weaken) B.weaken.weaken R.weaken.weaken
      z.weaken.weaken b.weaken.weaken X.weaken.weaken (.bound 1) .newest D.weaken.weaken)))

@[simp] theorem ng_dense_op_closed_l {n d} (φ : UnarySchema (n+3)) (e : Fin n → Term d)
    (B R z b X k D : Term d) (he : ∀ i, (e i).freeSupport = [])
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = [])
    (hb : b.freeSupport = []) (hX : X.freeSupport = []) (hk : k.freeSupport = []) (hD : D.freeSupport = []) :
    (ng_dense_op_m φ e B R z b X k D).FreeClosed := by
  simp -implicitDefEqProofs [ng_dense_op_m, Definitional.Formula.FreeClosed, *]

theorem ng_dense_op_sat_l (hE : Extensional M) {n d} (φ : UnarySchema (n+3)) (ρ : Env M d)
    (e : Fin n → Term d) (B R z b X k D : Term d) :
    Formula.satisfies ρ (ng_dense_op_m φ e B R z b X k D) ↔
      Ng_dense_op_d φ ⟨fun i => (e i).eval ρ, ρ.free⟩ (B.eval ρ) (R.eval ρ) (z.eval ρ)
        (b.eval ρ) (X.eval ρ) (k.eval ρ) (D.eval ρ) := by
  simp only [ng_dense_op_m, Ng_dense_op_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, ng_rule_decide_sat_l hE, Definitional.Term.eval_weaken]
  rfl

def Ng_select_at_d (I : kpair_convention_l.Interpretation M) {n}
    (φ : UnarySchema (n+3)) (ρ : Env M n) (B R z b ω l F t : M.Domain) : Prop :=
  ∃ f p, Fseq_end_d I ω F f p ∧ Ng_rule_d φ ρ B R z b l f p t

def ng_select_at_m {n d} (φ : UnarySchema (n+3)) (e : Fin n → Term d)
    (B R z b ω l F t : Term d) : Formula 1 d :=
  .existsE (.existsE (.conj (fseq_end_m (𝒞 := kpair_convention_l)
    ω.weaken.weaken F.weaken.weaken (.bound 1) .newest)
    (ng_rule_m φ (fun i => (e i).weaken.weaken) B.weaken.weaken R.weaken.weaken z.weaken.weaken
      b.weaken.weaken l.weaken.weaken (.bound 1) .newest t.weaken.weaken)))

@[simp] theorem ng_select_at_closed_l {n d} (φ : UnarySchema (n+3)) (e : Fin n → Term d)
    (B R z b ω l F t : Term d) (he : ∀ i, (e i).freeSupport = [])
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = [])
    (hb : b.freeSupport = []) (hω : ω.freeSupport = []) (hl : l.freeSupport = [])
    (hF : F.freeSupport = []) (ht : t.freeSupport = []) : (ng_select_at_m φ e B R z b ω l F t).FreeClosed := by
  simp -implicitDefEqProofs [ng_select_at_m, Definitional.Formula.FreeClosed, *]

theorem ng_select_at_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {n d} (φ : UnarySchema (n+3)) (ρ : Env M d) (e : Fin n → Term d) (B R z b ω l F t : Term d) :
    Formula.satisfies ρ (ng_select_at_m φ e B R z b ω l F t) ↔
      Ng_select_at_d I φ ⟨fun i => (e i).eval ρ, ρ.free⟩ (B.eval ρ) (R.eval ρ) (z.eval ρ)
        (b.eval ρ) (ω.eval ρ) (l.eval ρ) (F.eval ρ) (t.eval ρ) := by
  simp only [ng_select_at_m, Ng_select_at_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fseq_end_sat_l I hE, ng_rule_sat_l hE, Definitional.Term.eval_weaken]
  rfl

def Ng_select_op_d (I : kpair_convention_l.Interpretation M) {n}
    (φ : UnarySchema (n+3)) (ρ : Env M n) (B R z b ω X u k t : M.Domain) : Prop :=
  ∃ l F, KPair_d M k l F ∧ (Ng_select_at_d I φ ρ B R z b ω l F t ∨
    ((¬ ∃ s, M.mem s X ∧ Ng_select_at_d I φ ρ B R z b ω l F s) ∧ t = u))

def ng_select_op_m {n d} (φ : UnarySchema (n+3)) (e : Fin n → Term d)
    (B R z b ω X u k t : Term d) : Formula 1 d :=
  .existsE (.existsE (.conj (kpair_m k.weaken.weaken (.bound 1) .newest) (.disj
    (ng_select_at_m φ (fun i => (e i).weaken.weaken) B.weaken.weaken R.weaken.weaken z.weaken.weaken
      b.weaken.weaken ω.weaken.weaken (.bound 1) .newest t.weaken.weaken)
    (.conj (.neg (.existsE (.conj (.mem .newest X.weaken.weaken.weaken)
      (ng_select_at_m φ (fun i => (e i).weaken.weaken.weaken) B.weaken.weaken.weaken
        R.weaken.weaken.weaken z.weaken.weaken.weaken b.weaken.weaken.weaken ω.weaken.weaken.weaken
        (.bound 2) (.bound 1) .newest)))) (Formula.extensionalEq t.weaken.weaken u.weaken.weaken)))))

@[simp] theorem ng_select_op_closed_l {n d} (φ : UnarySchema (n+3)) (e : Fin n → Term d)
    (B R z b ω X u k t : Term d) (he : ∀ i, (e i).freeSupport = [])
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = [])
    (hb : b.freeSupport = []) (hω : ω.freeSupport = []) (hX : X.freeSupport = [])
    (hu : u.freeSupport = []) (hk : k.freeSupport = []) (ht : t.freeSupport = []) :
    (ng_select_op_m φ e B R z b ω X u k t).FreeClosed := by
  simp -implicitDefEqProofs [ng_select_op_m, Definitional.Formula.FreeClosed, *]

theorem ng_select_op_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {n d} (φ : UnarySchema (n+3)) (ρ : Env M d) (e : Fin n → Term d) (B R z b ω X u k t : Term d) :
    Formula.satisfies ρ (ng_select_op_m φ e B R z b ω X u k t) ↔
      Ng_select_op_d I φ ⟨fun i => (e i).eval ρ, ρ.free⟩ (B.eval ρ) (R.eval ρ) (z.eval ρ)
        (b.eval ρ) (ω.eval ρ) (X.eval ρ) (u.eval ρ) (k.eval ρ) (t.eval ρ) := by
  simp only [ng_select_op_m, Ng_select_op_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, Formula.satisfies_disj_iff, ng_select_at_sat_l I hE,
    Formula.satisfies_neg_iff, Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    Definitional.Term.eval_weaken]
  rfl

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

/-- 两张运算图均实际存在；唯一额外集合界是所有 B 的子集属于 X。 -/
theorem ng_operations_l {n} (φ : UnarySchema (n+3)) (ρ : Env M n) (B R z b ω : M.Domain)
    {X u T S D} (hu : M.mem u X) (hX : ∀ A, M.MemberSubset A B → M.mem A X)
    (hD : M.IsCartesianProduct I D T S) : ∃ K L,
      M.IsSetFunctionFromTo I K D X ∧ M.IsSetFunctionFromTo I L D X ∧
      (∀ k A, Entry_d M k A K → Ng_dense_op_d φ ρ B R z b X k A) ∧
      (∀ k t, Entry_d M k t L → Ng_select_op_d I φ ρ B R z b ω X u k t) := by
  classical
  let η := ((((((ρ.push B).push R).push z).push b).push ω).push X).push u
  let ψ : BinarySchema (n+7) := {
    body := ng_dense_op_m φ (fun i => .bound ⟨i.val+9, by omega⟩)
      (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 3) (.bound 1) .newest }
  let χ : BinarySchema (n+7) := {
    body := ng_select_op_m φ (fun i => .bound ⟨i.val+9, by omega⟩)
      (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hψ k A : ψ.denote η k A ↔ Ng_dense_op_d φ ρ B R z b X k A := ng_dense_op_sat_l hZFC.1 _ _ _ _ _ _ _ _ _ _
  have hχ k t : χ.denote η k t ↔ Ng_select_op_d I φ ρ B R z b ω X u k t := ng_select_op_sat_l I hZFC.1 _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨K, hK, hk⟩ := ZFC.uniformize_formula_l I hZFC ψ η (X := D) (Y := X) (by
    intro k hk
    obtain ⟨l, _, f, _, hlf⟩ := (hD k).mp hk
    obtain ⟨A, hA⟩ := ng_rule_decide_exists_l hZF φ ρ B R z b X l f
    exact ⟨A, hX A (fun p hp => ((hA p).mp hp).1), (hψ k A).mpr ⟨l, f, hlf, hA⟩⟩)
  obtain ⟨L, hL, hl⟩ := ZFC.uniformize_formula_l I hZFC χ η (X := D) (Y := X) (by
    intro k hk
    obtain ⟨l, _, F, _, hlf⟩ := (hD k).mp hk
    by_cases h : ∃ t, M.mem t X ∧ Ng_select_at_d I φ ρ B R z b ω l F t
    · obtain ⟨t, ht, h⟩ := h
      exact ⟨t, ht, (hχ k t).mpr ⟨l, F, hlf, Or.inl h⟩⟩
    · exact ⟨u, hu, (hχ k u).mpr ⟨l, F, hlf, Or.inr ⟨h, rfl⟩⟩⟩)
  exact ⟨K, L, hK, hL, fun k A h => (hψ k A).mp (hk k A h), fun k t h => (hχ k t).mp (hl k t h)⟩

omit hZFC in
/-- 规则正文自由闭合，故有限赋值相同便决定同一个名称选择关系。 -/
theorem ng_rule_env_l (hE : Extensional M) {n} (φ : UnarySchema (n+3))
    (ρ σ : Env M n) (he : ∀ i, ρ.bound i = σ.bound i) (B R z b l f p t) :
    Ng_rule_d φ ρ B R z b l f p t ↔ Ng_rule_d φ σ B R z b l f p t := by
  unfold Ng_rule_d
  apply and_congr_right
  intro _
  iterate 5 (apply exists_congr; intro)
  iterate 4 apply and_congr Iff.rfl
  exact forces_env_l hE φ.body φ.freeClosed _ _
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl he)))) p

omit hZFC in
theorem ng_dense_env_l (hE : Extensional M) {n} (φ : UnarySchema (n+3))
    (ρ σ : Env M n) (he : ∀ i, ρ.bound i = σ.bound i) (B R z b X k D) :
    Ng_dense_op_d φ ρ B R z b X k D ↔ Ng_dense_op_d φ σ B R z b X k D := by
  simp only [Ng_dense_op_d, Ng_rule_decide_d, Ng_rule_has_d, Neg_d,
    ng_rule_env_l hE φ ρ σ he]

omit hZFC in
theorem ng_select_env_l (J : kpair_convention_l.Interpretation M) (hE : Extensional M) {n} (φ : UnarySchema (n+3))
    (ρ σ : Env M n) (he : ∀ i, ρ.bound i = σ.bound i) (B R z b ω X u k t) :
    Ng_select_op_d J φ ρ B R z b ω X u k t ↔ Ng_select_op_d J φ σ B R z b ω X u k t := by
  simp only [Ng_select_op_d, Ng_select_at_d, ng_rule_env_l hE φ ρ σ he]

end YesMetaZFC.Model.Forcing.Internal
