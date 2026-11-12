import YesMetaZFC.Model.SetTheory.Internal.Theory
import YesMetaZFC.SetTheory.CumulativeClosure
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph
import YesMetaZFC.Model.SetTheory.Internal.TupleCode

/-! # 完整类型的变量名、常量名与赋值

内部自然数 i<n 表示第 i 个自由变量，n 表示指定常量 δ，(x,x) 表示集合常量 x。
有序对不传递，故两种名字互不混淆。任意内部有限名字列实际生成唯一赋值列；
列外取 δ，量词仍由原满足关系更新坐标。这里没有把内部有限列限制为外部有限列。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Tn_name_d (n U a : M.Domain) : Prop :=
  M.mem a n ∨ a = n ∨ ∃ x, M.mem x U ∧ KPair_d M a x x

def tn_name_m {d} (n U a : Term d) : Formula 1 d := .disj (.mem a n)
  (.disj (Formula.extensionalEq a n) (Formula.existsMem U (kpair0_m a.weaken .newest .newest)))
derive_free_closed tn_name_m

theorem tn_name_delta_l {d} (n U a : Term d) : (tn_name_m n U a).IsDelta0 :=
  .disj (.mem _ _) (.disj (.atom _ _ _) (.existsMem _ (kpair0_delta_l ..)))

theorem tn_name_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n U a : Term d) :
    Formula.satisfies ρ (tn_name_m n U a) ↔ Tn_name_d (n.eval ρ) (U.eval ρ) (a.eval ρ) := by
  simp only [tn_name_m, Tn_name_d, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_existsMem_iff, kpair0_sat_l hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

def Tn_names_d (n U N : M.Domain) : Prop := ∀ a, M.mem a N ↔ Tn_name_d n U a

theorem tn_names_exists_l (hZF : M.Models ZF) (n U : M.Domain) : ∃ N, Tn_names_d n U N := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨m, hm⟩ := KP.exists_successor (ZF.modelsKP hZF) n
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I U U
  obtain ⟨B, hB⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) m P
  let φ : UnarySchema 2 := { body := tn_name_m (.bound 2) (.bound 1) .newest }
  let ρ : Env M 2 := ⟨Fin.cases U (fun _ => n), fun _ => n⟩
  obtain ⟨N, sep⟩ := ZF.separation_exists_d hZF φ ρ B
  have sat a : φ.denote ρ a ↔ Tn_name_d n U a := tn_name_sat_l hZF.1 ..
  refine ⟨N, fun a => (sep a).trans ((and_congr_right fun _ => sat a).trans ⟨And.right, fun ha => ⟨?_, ha⟩⟩)⟩
  rcases ha with ha | ha | ⟨x, hx, code⟩
  · exact (hB a).mpr (Or.inl ((hm a).mpr (Or.inl ha)))
  · exact (hB a).mpr (Or.inl ((hm a).mpr (Or.inr (ha ▸ fun _ => Iff.rfl))))
  · exact (hB a).mpr (Or.inr ((hP a).mpr ⟨x, hx, x, hx, code⟩))

def Tn_value_d (n s δ a x : M.Domain) : Prop :=
  Rd_entry_d a x s ∨ (a = n ∧ x = δ) ∨ KPair_d M a x x

def tn_value_m {d} (n s δ a x : Term d) : Formula 1 d := .disj (rd_entry0_m a x s)
  (.disj (.conj (Formula.extensionalEq a n) (Formula.extensionalEq x δ)) (kpair0_m a x x))
derive_free_closed tn_value_m

theorem tn_value_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n s δ a x : Term d) :
    Formula.satisfies ρ (tn_value_m n s δ a x) ↔
      Tn_value_d (n.eval ρ) (s.eval ρ) (δ.eval ρ) (a.eval ρ) (x.eval ρ) := by
  simp only [tn_value_m, Tn_value_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, rd_entry0_sat_l hE, kpair0_sat_l hE]

theorem tn_value_unique_l (hKP : M.Models KP) {n s δ Z a x y : M.Domain}
    (hn : M.IsOrdinal n) (hs : Fn0_d n Z s) (hx : Tn_value_d n s δ a x) (hy : Tn_value_d n s δ a y) : x = y := by
  have hf := fn0_function_l hKP hs
  have disjoint z (hz : M.mem a n) (hp : KPair_d M a z z) : False :=
    hp.not_transitive_l M (KP.mem_irrefl_d hKP) (hn.mem hz).transitive
  rcases hx with hx | ⟨rfl, rfl⟩ | hx <;> rcases hy with hy | ⟨he, rfl⟩ | hy
  · exact hf.1.2 a x y hx hy
  · exact (KP.mem_irrefl_d hKP n (he ▸ hf.input_mem_of_pairMember hx)).elim
  · exact (disjoint y (hf.input_mem_of_pairMember hx) hy).elim
  · exact (KP.mem_irrefl_d hKP a (hf.input_mem_of_pairMember hy)).elim
  · rfl
  · exact (hy.not_transitive_l M (KP.mem_irrefl_d hKP) hn.transitive).elim
  · exact (disjoint x (hf.input_mem_of_pairMember hy) hx).elim
  · exact (hx.not_transitive_l M (KP.mem_irrefl_d hKP) (he.symm ▸ hn.transitive)).elim
  · exact (kpair_injective_l M hx hy).1

theorem tn_value_exists_l (hKP : M.Models KP) {n s δ U Z a : M.Domain}
    (hs : Fn0_d n Z s) (hδ : M.mem δ Z) (hU : M.MemberSubset U Z) (ha : Tn_name_d n U a) :
    ∃ x, M.mem x Z ∧ Tn_value_d n s δ a x := by
  rcases ha with ha | rfl | ⟨x, hx, hp⟩
  · obtain ⟨x, hx, he⟩ := (fn0_function_l hKP hs).2.2 a ha
    exact ⟨x, hx, Or.inl he⟩
  · exact ⟨δ, hδ, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · exact ⟨x, hU x hx, Or.inr (Or.inr hp)⟩

def Tn_assign_d (n s δ e r : M.Domain) : Prop :=
  (∀ p, M.mem p r → ∃ i x, KPair_d M p i x) ∧
    ∀ i x, Rd_entry_d i x r ↔ ∃ a, Rd_entry_d i a e ∧ Tn_value_d n s δ a x

def tn_assign_m {d} (n s δ e r : Term d) : Formula 1 d :=
  .conj (Formula.isRelation kpair_convention_l r) (.forallE (.forallE (.iff
    (rd_entry0_m (.bound 1) .newest r.weaken.weaken) (.existsE
      (.conj (rd_entry0_m (.bound 2) .newest e.weaken.weaken.weaken)
        (tn_value_m n.weaken.weaken.weaken s.weaken.weaken.weaken δ.weaken.weaken.weaken .newest (.bound 1)))))))
derive_free_closed tn_assign_m

theorem tn_assign_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (n s δ e r : Term d) :
    Formula.satisfies ρ (tn_assign_m n s δ e r) ↔
      Tn_assign_d (n.eval ρ) (s.eval ρ) (δ.eval ρ) (e.eval ρ) (r.eval ρ) := by
  simp only [tn_assign_m, Tn_assign_d, Formula.satisfies_conj_iff,
    Formula.satisfies_isRelation_iff (kp_pair_l hKP), Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, rd_entry0_sat_l hKP.1, Formula.satisfies_exists_iff,
    tn_value_sat_l hKP.1, Definitional.Term.eval_weaken]
  rfl

theorem tn_assign_unique_l (hKP : M.Models KP) {n s δ e r t : M.Domain}
    (hr : Tn_assign_d n s δ e r) (ht : Tn_assign_d n s δ e t) : r = t :=
  Structure.IsSetRelation.eq_of_pairMember_iff (𝕀 := kp_pair_l hKP) hKP.1 hr.1 ht.1
    (fun i x => (hr.2 i x).trans (ht.2 i x).symm)

/-- 每一条合法名字列都生成实际函数；存在性和唯一性均来自原公式。 -/
theorem tn_assign_exists_l (hZF : M.Models ZF) {n s δ U Z N b e : M.Domain}
    (hn : M.IsOrdinal n) (hs : Fn0_d n Z s) (hδ : M.mem δ Z) (hU : M.MemberSubset U Z)
    (names : Tn_names_d n U N) (he : Fn0_d b N e) :
    ∃ r, Tn_assign_d n s δ e r ∧ Fn0_d b Z r := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hf := fn0_function_l (ZF.modelsKP hZF) he
  let φ : BinarySchema 4 := { body := .existsE (.conj (rd_entry0_m (.bound 2) .newest (.bound 3))
    (tn_value_m (.bound 6) (.bound 5) (.bound 4) .newest (.bound 1))) }
  let ρ : Env M 4 := ⟨Fin.cases e (Fin.cases δ (Fin.cases s (fun _ => n))), fun _ => n⟩
  have sat i x : φ.denote ρ i x ↔ ∃ a, Rd_entry_d i a e ∧ Tn_value_d n s δ a x := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, tn_value_sat_l hZF.1]; rfl
  have total i (hi : M.mem i b) : ∃ x, M.mem x Z ∧ φ.denote ρ i x := by
    obtain ⟨a, ha, hia⟩ := hf.2.2 i hi
    obtain ⟨x, hx, value⟩ := tn_value_exists_l (ZF.modelsKP hZF) hs hδ hU ((names a).mp ha)
    exact ⟨x, hx, (sat i x).mpr ⟨a, hia, value⟩⟩
  have unique i x y (hx : φ.denote ρ i x) (hy : φ.denote ρ i y) : x = y := by
    obtain ⟨a, ha, hx⟩ := (sat i x).mp hx
    obtain ⟨a', ha', hy⟩ := (sat i y).mp hy
    have eq := hf.1.2 i a a' ha ha'
    subst a'
    exact tn_value_unique_l (ZF.modelsKP hZF) hn hs hx hy
  obtain ⟨r, hr, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ
    (fun i hi => (total i hi).imp fun _ hx => hx.2) (fun i _ => unique i)
    (fun i x hi hx => by obtain ⟨y, hy, hy'⟩ := total i hi; exact unique i x y hx hy' ▸ hy)
  refine ⟨r, ⟨hr.1.1, fun i x => (spec i x).trans ((and_congr_right fun _ => sat i x).trans
    ⟨And.right, fun hh => ⟨?_, hh⟩⟩)⟩, fn0_of_function_l (ZF.modelsKP hZF) hr⟩
  obtain ⟨a, ha, _⟩ := hh
  exact hf.input_mem_of_pairMember ha

end YesMetaZFC.SetTheory.Internal

/-! ## 原名字列对平坦元组的有界求值矩阵

名字仍是原 Kuratowski 码；实现元组与完整赋值用平坦图。
矩阵只量化实际的 ω、对象载体和名字所在秩层，因而可以穿过后继秩层。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def fp_entry0_m {d} (ω i x f : Term d) : Formula 1 d :=
  Formula.existsMem f (fp_pair0_m ω.weaken i.weaken x.weaken .newest)
derive_free_closed fp_entry0_m

theorem fp_entry0_delta_l {d} (ω i x f : Term d) : (fp_entry0_m ω i x f).IsDelta0 :=
  .existsMem _ (fp_pair0_delta_l ..)

theorem fp_entry0_sat_l (hKPi : M.Models KPi) {d} (ρ : Env M d) (ω i x f : Term d)
    (hω : M.IsOmega (ω.eval ρ)) : Formula.satisfies ρ (fp_entry0_m ω i x f) ↔
      M.PairMember (fp_interpretation_l hKPi) (i.eval ρ) (x.eval ρ) (f.eval ρ) := by
  have hKP := (KPi.models_iff_l.mp hKPi).1
  have read p := fp_pair0_sat_l hKP (ρ.push p) ω.weaken i.weaken x.weaken .newest
    (by simpa only [Definitional.Term.eval_weaken] using hω.1)
  simp only [fp_entry0_m, Formula.satisfies_existsMem_iff, read,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun ⟨p, hp, code⟩ => ⟨p, (fp_fixed_l hKP.1 hω).mpr code, hp⟩,
    fun ⟨p, code, hp⟩ => ⟨p, hp, (fp_fixed_l hKP.1 hω).mp code⟩⟩

variable (J : FlatPairing.convention.Interpretation M)

def Tf_value_d (n h δ a x : M.Domain) : Prop :=
  M.PairMember J a x h ∨ (a = n ∧ x = δ) ∨ KPair_d M a x x

def tf_value0_m {d} (ω n h δ a x : Term d) : Formula 1 d := .disj (fp_entry0_m ω a x h)
  (.disj (.conj (Formula.extensionalEq a n) (Formula.extensionalEq x δ)) (kpair0_m a x x))
derive_free_closed tf_value0_m

theorem tf_value0_delta_l {d} (ω n h δ a x : Term d) : (tf_value0_m ω n h δ a x).IsDelta0 :=
  .disj (fp_entry0_delta_l ..) (.disj (.conj (.atom _ _ _) (.atom _ _ _)) (kpair0_delta_l ..))

theorem tf_value0_sat_l (hKPi : M.Models KPi) {d} (ρ : Env M d) (ω n h δ a x : Term d)
    (hω : M.IsOmega (ω.eval ρ)) : Formula.satisfies ρ (tf_value0_m ω n h δ a x) ↔
      Tf_value_d (fp_interpretation_l hKPi) (n.eval ρ) (h.eval ρ) (δ.eval ρ) (a.eval ρ) (x.eval ρ) := by
  simp only [tf_value0_m, Tf_value_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    fp_entry0_sat_l hKPi _ _ _ _ _ hω, Formula.satisfies_extensionalEq_iff_eq (KPi.models_iff_l.mp hKPi).1.1,
    kpair0_sat_l (KPi.models_iff_l.mp hKPi).1.1]

def Tf_fill_d (ω X Z n h δ b e g : M.Domain) : Prop := ∀ i, M.mem i ω → ∀ x, M.mem x X →
  (M.PairMember J i x g ↔ (M.mem i b ∧ ∃ a, M.mem a Z ∧ Rd_entry_d i a e ∧ Tf_value_d J n h δ a x) ∨
    (¬ M.mem i b ∧ x = δ))

def tf_fill0_m {d} (ω X Z n h δ b e g : Term d) : Formula 1 d := set[d] ⟪∀ i ∈ ⌜ω⌝ₛ, ∀ x ∈ ⌜X⌝ₛ,
  ⌜fp_entry0_m⌝ₚ(⌜ω⌝ₛ, i, x, ⌜g⌝ₛ) ↔
    (i ∈ ⌜b⌝ₛ ∧ (∃ a ∈ ⌜Z⌝ₛ, ⌜rd_entry0_m⌝ₚ(i, a, ⌜e⌝ₛ) ∧ ⌜tf_value0_m⌝ₚ(⌜ω⌝ₛ, ⌜n⌝ₛ, ⌜h⌝ₛ, ⌜δ⌝ₛ, a, x))) ∨
    (¬ i ∈ ⌜b⌝ₛ ∧ x = ⌜δ⌝ₛ)⟫
derive_free_closed tf_fill0_m

theorem tf_fill0_delta_l {d} (ω X Z n h δ b e g : Term d) : (tf_fill0_m ω X Z n h δ b e g).IsDelta0 :=
  .forallMem _ (.forallMem _ (.iff (fp_entry0_delta_l ..) (.disj
    (.conj (.mem _ _) (.existsMem _ (.conj (rd_entry0_delta_l ..) (tf_value0_delta_l ..))))
    (.conj (.neg (.mem _ _)) (.atom _ _ _)))))

theorem tf_fill0_sat_l (hKPi : M.Models KPi) {d} (ρ : Env M d) (ω X Z n h δ b e g : Term d)
    (hω : M.IsOmega (ω.eval ρ)) : Formula.satisfies ρ (tf_fill0_m ω X Z n h δ b e g) ↔
      Tf_fill_d (fp_interpretation_l hKPi) (ω.eval ρ) (X.eval ρ) (Z.eval ρ) (n.eval ρ) (h.eval ρ)
        (δ.eval ρ) (b.eval ρ) (e.eval ρ) (g.eval ρ) := by
  have entry i x := fp_entry0_sat_l hKPi ((ρ.push i).push x) ω.weaken.weaken
    (.newest : Term (d+1)).weaken .newest g.weaken.weaken
    (by simpa only [Definitional.Term.eval_weaken] using hω)
  have value i x a := tf_value0_sat_l hKPi (((ρ.push i).push x).push a)
    ω.weaken.weaken.weaken n.weaken.weaken.weaken h.weaken.weaken.weaken δ.weaken.weaken.weaken
    .newest (.newest : Term (d+2)).weaken
    (by simpa only [Definitional.Term.eval_weaken] using hω)
  simp only [tf_fill0_m, Tf_fill_d, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_disj_iff, Formula.satisfies_conj_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq (KPi.models_iff_l.mp hKPi).1.1,
    entry, rd_entry0_sat_l (KPi.models_iff_l.mp hKPi).1.1, value,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

variable (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

theorem tf_value_recode_l {n s h δ a x : M.Domain} (agree : Sx_graph_d Q K s h) :
    Tf_value_d K n h δ a x ↔ Tn_value_d n s δ a x :=
  or_congr (agree a x) Iff.rfl

/-- 有界矩阵恰好要求原完整赋值的逐点重编码，不依赖源内拥有原图。 -/
theorem tf_fill_iff_l {ω X Z n s h δ b e r f g : M.Domain}
    (hZ : M.TransitiveSet Z) (he : M.mem e Z) (tuple : Sx_graph_d Q K s h)
    (assign : Tn_assign_d n s δ e r) (fill : Senv_fill_d Q ω δ b r f)
    (hf : M.IsSetFunctionFromTo Q f ω X) (hg : M.IsSetFunctionFromTo K g ω X) :
    Tf_fill_d K ω X Z n h δ b e g ↔ Sx_graph_d Q K f g := by
  have value i x : (∃ a, M.mem a Z ∧ Rd_entry_d i a e ∧ Tf_value_d K n h δ a x) ↔ Rd_entry_d i x r := by
    refine Iff.trans ?_ (assign.2 i x).symm
    exact ⟨fun ⟨a, _, ha, hx⟩ => ⟨a, ha, (tf_value_recode_l hZF tuple).mp hx⟩,
      fun ⟨a, ha, hx⟩ => ⟨a, (rd_entry_transitive_l hZ he ha).2, ha, (tf_value_recode_l hZF tuple).mpr hx⟩⟩
  have old i x (hi : M.mem i ω) : M.PairMember Q i x f ↔
      (M.mem i b ∧ ∃ a, M.mem a Z ∧ Rd_entry_d i a e ∧ Tf_value_d K n h δ a x) ∨ (¬ M.mem i b ∧ x = δ) :=
    (fill.2 i x).trans ((and_iff_right hi).trans (or_congr (and_congr Iff.rfl (value i x).symm) Iff.rfl))
  constructor
  · intro matrix i x
    by_cases hi : M.mem i ω
    · by_cases hx : M.mem x X
      · exact (matrix i hi x hx).trans (old i x hi).symm
      · exact iff_of_false (fun h => hx (hg.output_mem_of_pairMember h)) (fun h => hx (hf.output_mem_of_pairMember h))
    · exact iff_of_false (fun h => hi (hg.input_mem_of_pairMember h)) (fun h => hi (hf.input_mem_of_pairMember h))
  · exact fun agree i hi x _ => (agree i x).trans (old i x hi)

end YesMetaZFC.SetTheory.Internal

/-! ## 用原名字列移动类型的实现元组

同一内部有限名字列可重复、置换指定点和集合常量。下面的有界矩阵生成
该列的平坦赋值；原 Kuratowski 元组仅用于证明，不改动任何类型查询码。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def tm_assign0_m {d} (ω Z A e ν E n h : Term d) : Formula 1 d := set[d] ⟪
  ∀ i ∈ ⌜n⌝ₛ, ∀ x ∈ ⌜A⌝ₛ, ⌜fp_entry0_m⌝ₚ(⌜ω⌝ₛ, i, x, ⌜h⌝ₛ) ↔
    (∃ a ∈ ⌜Z⌝ₛ, ⌜rd_entry0_m⌝ₚ(i, a, ⌜E⌝ₛ) ∧ ⌜tn_value_m⌝ₚ(⌜e⌝ₛ, ⌜e⌝ₛ, ⌜ν⌝ₛ, a, x))⟫
derive_free_closed tm_assign0_m

theorem tm_assign0_delta_l {d} (ω Z A e ν E n h : Term d) :
    (tm_assign0_m ω Z A e ν E n h).IsDelta0 :=
  .forallMem _ (.forallMem _ (.iff (fp_entry0_delta_l ..) (.existsMem _
    (.conj (rd_entry0_delta_l ..) (.disj (rd_entry0_delta_l ..)
      (.disj (.conj (.atom _ _ _) (.atom _ _ _)) (kpair0_delta_l ..)))))))

def Tm_assign_d (K : FlatPairing.convention.Interpretation M) (Z A e ν E n h : M.Domain) : Prop :=
  ∀ i, M.mem i n → ∀ x, M.mem x A → (M.PairMember K i x h ↔
    ∃ a, M.mem a Z ∧ Rd_entry_d i a E ∧ Tn_value_d e e ν a x)

theorem tm_assign0_sat_l (hKPi : M.Models KPi) {d} (ρ : Env M d) (ω Z A e ν E n h : Term d)
    (hω : M.IsOmega (ω.eval ρ)) : Formula.satisfies ρ (tm_assign0_m ω Z A e ν E n h) ↔
      Tm_assign_d (fp_interpretation_l hKPi) (Z.eval ρ) (A.eval ρ) (e.eval ρ) (ν.eval ρ)
        (E.eval ρ) (n.eval ρ) (h.eval ρ) := by
  have entry i x := fp_entry0_sat_l hKPi ((ρ.push i).push x) ω.weaken.weaken
    (.newest : Term (d+1)).weaken .newest h.weaken.weaken
    (by simpa only [Definitional.Term.eval_weaken] using hω)
  simp only [tm_assign0_m, Tm_assign_d, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, entry,
    rd_entry0_sat_l (KPi.models_iff_l.mp hKPi).1.1, tn_value_sat_l (KPi.models_iff_l.mp hKPi).1.1,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

variable (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

theorem tm_assign_iff_l {Z A e ν E n h s : M.Domain} (names : Fn0_d n Z E)
    (assign : Tn_assign_d e e ν E s) (tuple : Fn0_d n A s) (flat : M.IsSetFunctionFromTo K h n A) :
    Tm_assign_d K Z A e ν E n h ↔ Sx_graph_d Q K s h := by
  have fn := fn0_function_l (ZF.modelsKP hZF) tuple
  have read i x : (∃ a, M.mem a Z ∧ Rd_entry_d i a E ∧ Tn_value_d e e ν a x) ↔ Rd_entry_d i x s :=
    ⟨fun ⟨a, _, ha, hx⟩ => (assign.2 i x).mpr ⟨a, ha, hx⟩,
      fun hx => by
        obtain ⟨a, ha, hx⟩ := (assign.2 i x).mp hx
        exact ⟨a, (fn0_function_l (ZF.modelsKP hZF) names).output_mem_of_pairMember ha, ha, hx⟩⟩
  constructor
  · intro matrix i x
    by_cases hi : M.mem i n
    · by_cases hx : M.mem x A
      · exact (matrix i hi x hx).trans (read i x)
      · exact iff_of_false (fun h => hx (flat.output_mem_of_pairMember h)) (fun h => hx (fn.output_mem_of_pairMember h))
    · exact iff_of_false (fun h => hi (flat.input_mem_of_pairMember h)) (fun h => hi (fn.input_mem_of_pairMember h))
  · exact fun agree i _ x _ => (agree i x).trans (read i x).symm

end YesMetaZFC.SetTheory.Internal

/-! ## 从实际元组自动恢复共同名字列

逐项把指定高度写为空名字，把其余实际对象写为原对角常量名。
函数图在内部由替换生成，长度可以非标准；不预设任何坐标顺序。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Tm_move_d (ν μ s r : M.Domain) : Prop := ∀ i x, Rd_entry_d i x r ↔
  ∃ y, Rd_entry_d i y s ∧ ((y = ν ∧ x = μ) ∨ (y ≠ ν ∧ x = y))

def Tm_quote_d (e ν s E : M.Domain) : Prop := ∀ i a, Rd_entry_d i a E ↔
  ∃ x, Rd_entry_d i x s ∧ ((x = ν ∧ a = e) ∨ (x ≠ ν ∧ KPair_d M a x x))

variable (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
include hZF

/-- 原元组是自动名字列的实际赋值；同一列在任意新高度的赋值恰好逐项移动该高度。 -/
theorem tm_quote_l {e ν n P Z A s : M.Domain} (he : ∀ x, ¬ M.mem x e)
    (names : Tn_names_d e P Z) (tuple : Fn0_d n A s)
    (values : ∀ i x, Rd_entry_d i x s → x = ν ∨ M.mem x P) :
    ∃ E, Fn0_d n Z E ∧ Tn_assign_d e e ν E s ∧ Tm_quote_d e ν s E ∧
      ∀ μ r, Tn_assign_d e e μ E r → Tm_move_d ν μ s r := by
  have fn := fn0_function_l (ZF.modelsKP hZF) tuple
  have empty : Fn0_d e A e := ⟨fun p hp => (he p hp).elim,
    fun i hi => (he i hi).elim, fun i hi => (he i hi).elim⟩
  let φ : BinarySchema 3 := { body := set[5] ⟪∃ x,
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 1 : Term 5)⌝ₛ, x, ⌜(.bound 2 : Term 5)⌝ₛ) ∧
    ((x = ⌜(.bound 3 : Term 5)⌝ₛ ∧ ⌜(.newest : Term 5)⌝ₛ = ⌜(.bound 4 : Term 5)⌝ₛ) ∨
      (¬ (x = ⌜(.bound 3 : Term 5)⌝ₛ) ∧ ⌜kpair0_m⌝ₚ(⌜(.newest : Term 5)⌝ₛ, x, x)))⟫ }
  let ρ : Env M 3 := ⟨Fin.cases s (Fin.cases ν (fun _ => e)), fun _ => e⟩
  have read i a : φ.denote ρ i a ↔ ∃ x, Rd_entry_d i x s ∧
      ((x = ν ∧ a = e) ∨ (x ≠ ν ∧ KPair_d M a x x)) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_disj_iff, Formula.satisfies_neg_iff, rd_entry0_sat_l hZF.1,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, kpair0_sat_l hZF.1]
    rfl
  have total i (hi : M.mem i n) : ∃ a, φ.denote ρ i a := by
    obtain ⟨x, _, hx⟩ := fn.2.2 i hi
    by_cases eq : x = ν
    · exact ⟨e, (read i e).mpr ⟨x, hx, Or.inl ⟨eq, rfl⟩⟩⟩
    · obtain ⟨a, ha⟩ := (Q).total x x
      exact ⟨a, (read i a).mpr ⟨x, hx, Or.inr ⟨eq, ha⟩⟩⟩
  have unique i a b (ha : φ.denote ρ i a) (hb : φ.denote ρ i b) : a = b := by
    obtain ⟨x, hx, ha⟩ := (read i a).mp ha
    obtain ⟨y, hy, hb⟩ := (read i b).mp hb
    have eq := fn.1.2 i x y hx hy
    subst y
    rcases ha with ⟨h, rfl⟩ | ⟨h, ha⟩ <;> rcases hb with ⟨h', rfl⟩ | ⟨h', hb⟩
    · rfl
    · exact (h' h).elim
    · exact (h h').elim
    · exact (Q).unique ha hb
  have bound i a (ha : φ.denote ρ i a) : M.mem a Z := by
    obtain ⟨x, hx, ⟨_, hae⟩ | ⟨hne, hp⟩⟩ := (read i a).mp ha
    · exact hae.symm ▸ (names e).mpr (Or.inr (Or.inl rfl))
    · exact (names a).mpr (Or.inr (Or.inr ⟨x, (values i x hx).resolve_left hne, hp⟩))
  obtain ⟨E, ef, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF Q φ ρ total
    (fun i _ => unique i) (fun i a _ => bound i a)
  have quote i a : Rd_entry_d i a E ↔ ∃ x, Rd_entry_d i x s ∧
      ((x = ν ∧ a = e) ∨ (x ≠ ν ∧ KPair_d M a x x)) :=
    (graph i a).trans ((and_congr_right fun _ => read i a).trans
      ⟨And.right, fun ⟨x, hx, ha⟩ => ⟨fn.input_mem_of_pairMember hx, x, hx, ha⟩⟩)
  have transfer {y a μ x} (mark : (y = ν ∧ a = e) ∨ (y ≠ ν ∧ KPair_d M a y y)) :
      Tn_value_d e e μ a x ↔ (y = ν ∧ x = μ) ∨ (y ≠ ν ∧ x = y) := by
    rcases mark with ⟨hy, ha⟩ | ⟨hne, code⟩
    · subst y a
      have v : Tn_value_d e e μ e μ := Or.inr (Or.inl ⟨rfl, rfl⟩)
      exact ⟨fun h => Or.inl ⟨rfl, tn_value_unique_l (ZF.modelsKP hZF) (Structure.IsOrdinal.of_no_members he) empty h v⟩,
        fun h => h.elim (fun h => h.2.symm ▸ v) (fun h => (h.1 rfl).elim)⟩
    · have v : Tn_value_d e e μ a y := Or.inr (Or.inr code)
      exact ⟨fun h => Or.inr ⟨hne, tn_value_unique_l (ZF.modelsKP hZF) (Structure.IsOrdinal.of_no_members he) empty h v⟩,
        fun h => h.elim (fun h => (hne h.1).elim) (fun h => h.2.symm ▸ v)⟩
  have select i y (hy : Rd_entry_d i y s) : ∃ a, Rd_entry_d i a E ∧
      ((y = ν ∧ a = e) ∨ (y ≠ ν ∧ KPair_d M a y y)) := by
    obtain ⟨a, _, ha⟩ := ef.2.2 i (fn.input_mem_of_pairMember hy)
    obtain ⟨x, hx, mark⟩ := (quote i a).mp ha
    exact ⟨a, ha, fn.1.2 i x y hx hy ▸ mark⟩
  have assign : Tn_assign_d e e ν E s := by
    refine ⟨fn.1.1, fun i x => ⟨?_, ?_⟩⟩
    · intro hx
      obtain ⟨a, ha, mark⟩ := select i x hx
      by_cases eq : x = ν
      · exact ⟨a, ha, (transfer mark).mpr (Or.inl ⟨eq, eq⟩)⟩
      · exact ⟨a, ha, (transfer mark).mpr (Or.inr ⟨eq, rfl⟩)⟩
    · rintro ⟨a, ha, value⟩
      obtain ⟨y, hy, mark⟩ := (quote i a).mp ha
      rcases (transfer mark).mp value with ⟨hyν, hxν⟩ | ⟨_, hxy⟩
      · exact (hyν.trans hxν.symm) ▸ hy
      · exact hxy.symm ▸ hy
  refine ⟨E, fn0_of_function_l (ZF.modelsKP hZF) ef, assign, quote, fun μ r hr i x => ?_⟩
  refine (hr.2 i x).trans ⟨?_, ?_⟩
  · rintro ⟨a, ha, value⟩
    obtain ⟨y, hy, mark⟩ := (quote i a).mp ha
    exact ⟨y, hy, (transfer mark).mp value⟩
  · rintro ⟨y, hy, move⟩
    obtain ⟨a, ha, mark⟩ := select i y hy
    exact ⟨a, ha, (transfer mark).mpr move⟩

end YesMetaZFC.SetTheory.Internal
