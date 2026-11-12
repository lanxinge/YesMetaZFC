import YesMetaZFC.Model.SetTheory.Types.Embedding
import YesMetaZFC.Model.SetTheory.Internal.Hereditary
import YesMetaZFC.SetTheory.Ord.Arithmetic.Comparison
import YesMetaZFC.Model.SetTheory.Internal.FiniteTailSource
import YesMetaZFC.Model.SetTheory.Types.MoveQuote
import YesMetaZFC.Model.SetTheory.Types.LowerSource

/-! # V(ν+ω) 中指定序数的完整类型

查询域固定，指定常量解释为 ν；零个自由变量的全部查询仍允许任意内部
有限参数列。类型值由同一条原公式定义，以便在 ZF 内收集其高度界。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Li_type_d (ω e U D ν t : M.Domain) : Prop := ∃ η X c R,
  M.IsOrdinalAddition I η ν ω ∧ V_d I η X ∧ Smem_d I c X R ∧ M.mem ν X ∧ M.MemberSubset U X ∧
    Tt_truth_d I ω c e e ν D t

def li_type_m {d} (ω e U D ν t : Term d) : Formula 1 d := set[d] ⟪∃ η X c R,
  ⌜Formula.isOrdinalAddition kpair_convention_l⌝ₚ(η, ⌜ν⌝ₛ, ⌜ω⌝ₛ) ∧
  ⌜v_m kpair_convention_l⌝ₚ(η, X) ∧ ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, X, R) ∧
  ⌜ν⌝ₛ ∈ X ∧ ⌜U⌝ₛ ⊆ X ∧ (∀ p, p ∈ ⌜t⌝ₛ ↔
    (p ∈ ⌜D⌝ₛ ∧ ⌜tt_query_m⌝ₚ(⌜ω⌝ₛ, c, ⌜e⌝ₛ, ⌜e⌝ₛ, ⌜ν⌝ₛ, p)))⟫
derive_free_closed li_type_m

theorem li_type_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω e U D ν t : Term d) :
    Formula.satisfies ρ (li_type_m ω e U D ν t) ↔
      Li_type_d I (ω.eval ρ) (e.eval ρ) (U.eval ρ) (D.eval ρ) (ν.eval ρ) (t.eval ρ) := by
  simp only [li_type_m, Li_type_d, Tt_truth_d, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_isOrdinalAddition_iff I hKP.1,
    v_sat_l I hKP.1, smem_sat_l I, Formula.satisfies_mem_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, tt_query_sat_l I hKP,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

variable (hZF : M.Models ZF)

include hZF in
/-- 任意超过参数秩的序数都有实际类型；没有使用外部真值或外部序数递归。 -/
theorem li_type_exists_l {ω e γ U D ν : M.Domain} (hω : M.IsOmega ω)
    (hU : V_d I γ U) (hν : M.IsOrdinal ν) (hγν : M.mem γ ν) :
    ∃ t, Li_type_d I ω e U D ν t := by
  obtain ⟨η, sum, _⟩ := ZF.ordinalAddition_existsUnique hZF I ν (hω.isOrdinal (ZF.modelsKP hZF))
  have hη := (ZF.ordinalAddition_isNormalOrdinalFunction hZF I hν).1.2 _ _ (hω.isOrdinal (ZF.modelsKP hZF)) sum
  obtain ⟨z, hz, hzω⟩ := hω.1.1
  have hνη := (ZF.ordinalAddition_mem_iff hZF I (hω.isOrdinal (ZF.modelsKP hZF)) sum).mpr
    (Or.inr ⟨z, hzω, (ZF.ordinalAddition_zero_iff hZF I hz).mpr rfl⟩)
  obtain ⟨X, hX⟩ := ZF.v_exists_l I hZF hη
  have point := ZF.v_ordinal_mem_l I hZF hX hνη
  obtain ⟨c, R, model⟩ := smdl_membership_l I hZF ⟨ν, point⟩
  obtain ⟨t, truth, _⟩ := tt_truth_exists_l I hZF ω c e e ν D
  exact ⟨t, η, X, c, R, sum, hX, model, point,
    ZF.v_mono_l I hZF hU hX (hη.transitive γ (hη.transitive ν hνη γ hγν)), truth⟩

include hZF in
/-- 每个固定高度的完整类型唯一，包含全部内部公式码。 -/
theorem Li_type_d.unique_l {ω e U D ν t u : M.Domain} (hω : M.IsOmega ω)
    (h : Li_type_d I ω e U D ν t) (k : Li_type_d I ω e U D ν u) : t = u := by
  obtain ⟨η, X, c, R, sum, hX, model, _, _, truth⟩ := h
  obtain ⟨θ, Y, d, S, sum', hY, model', _, _, truth'⟩ := k
  obtain ⟨a, _, unique⟩ := ZF.ordinalAddition_existsUnique hZF I ν (hω.isOrdinal (ZF.modelsKP hZF))
  have eqη := (unique η sum).trans (unique θ sum').symm
  subst θ
  have eqX := ZF.v_unique_l I hZF hX hY
  subst Y
  obtain ⟨eqc, eqR⟩ := smem_unique_l I hZF.1 model' model
  subst d S
  exact hZF.1.eq_of_same_members t u (fun p => (truth p).trans (truth' p).symm)

/-- 零变量与空元组的真实实现；参数域和指定序数来自原类型公式的守卫。 -/
theorem Li_type_d.realized_l {ω e U D ν t : M.Domain} (he : ∀ x, ¬ M.mem x e) (heω : M.mem e ω)
    (pool : Tt_pool_d I ω e U D) (h : Li_type_d I ω e U D ν t) :
    ∃ η X c R, M.IsOrdinalAddition I η ν ω ∧ V_d I η X ∧ Smem_d I c X R ∧
      Tt_realized_d I ω c X R e e ν U D t := by
  obtain ⟨η, X, c, R, sum, hX, model, point, constants, truth⟩ := h
  have tuple : Fn0_d e X e := ⟨fun p hp => (he p hp).elim,
    fun i hi => (he i hi).elim, fun i hi => (he i hi).elim⟩
  exact ⟨η, X, c, R, sum, hX, model, model.1, heω, tuple, point, constants, pool, truth⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 同一完整类型的指定点与有限参数真值

第一个公式变量解释为指定序数，其余变量解释为共同参数域中的原对象。
查询在两个实现之前固定，因此同一类型的成员关系直接给出真值对应。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

/-- 原公式的纸面赋值 (δ,a₀,…,aₖ₋₁)，不选择任何载体基点。 -/
def Tt_realized_d.point_env_l {ω c X R n s δ U D t : M.Domain}
    (h : Tt_realized_d I ω c X R n s δ U D t) {k : Nat} (a : Fin k → M.Domain)
    (ha : ∀ i, M.mem (a i) U) : Env (smdl_structure_l I (R := R) h.model.2.1) (k+1) :=
  ⟨Fin.cases ⟨δ, h.point⟩ (fun i => ⟨a i, h.constants (a i) (ha i)⟩), fun _ => ⟨δ, h.point⟩⟩

variable (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)

/-- 包括重复参数和任意参数顺序；两边可位于不同秩层、具有不同指定点。 -/
theorem Tt_realized_d.point_congr_l {ω n U D t c X R s δ d Y S r ε : M.Domain}
    (hω : M.IsOmega ω) (h : Tt_realized_d Q ω c X R n s δ U D t)
    (g : Tt_realized_d Q ω d Y S n r ε U D t) {k : Nat}
    (φ : Formula 1 (k+1)) (hφ : φ.FreeClosed) (a : Fin k → M.Domain) (ha : ∀ i, M.mem (a i) U) :
    Formula.satisfies (h.point_env_l Q a ha) φ ↔ Formula.satisfies (g.point_env_l Q a ha) φ := by
  obtain ⟨b, hb⟩ := Classical.axiomOfChoice (fun i => (Q).total (a i) (a i))
  let v : Fin (k+1) → M.Domain := Fin.cases n b
  have names : ∀ i, Tn_name_d n U (v i) :=
    Fin.cases (Or.inr (Or.inl rfl)) (fun i => Or.inr (Or.inr ⟨a i, ha i, hb i⟩))
  have values {c X R s δ} (h : Tt_realized_d Q ω c X R n s δ U D t) :
      ∀ i, Tn_value_d n s δ (v i) ((h.point_env_l Q a ha).bound i).val :=
    Fin.cases (Or.inr (Or.inl ⟨rfl, rfl⟩)) (fun i => Or.inr (Or.inr (hb i)))
  obtain ⟨p, _, read⟩ := tt_fixed_query_l hZF hω h.pool φ hφ v names
  exact (read c X R s δ t h (h.point_env_l _ a ha) (values h)).symm.trans
    (read d Y S r ε t g (g.point_env_l _ a ha) (values g))

end YesMetaZFC.SetTheory.Internal

/-! ## 在 V(ν+ω) 中统一读取 V(ν+k) 的完整类型

公式自行求出层高、秩层和移动后的元组，只把原名字列及候选类型作为参数。
内部有限长度 k 和元组长度 n 都是对象自然数；读取覆盖原查询域的全部成员。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def tm_type_m {d} (ω C κ k n Z E δ e ν t : Term d) : Formula 1 d := set[d] ⟪∃ β A h,
  ⌜Formula.isOrdinalAddition kpair_convention_l⌝ₚ(β, ⌜ν⌝ₛ, ⌜k⌝ₛ) ∧
  ⌜v_m FlatPairing.convention⌝ₚ(β, A) ∧
  ⌜Formula.isFunctionFromTo FlatPairing.convention⌝ₚ(h, ⌜n⌝ₛ, A) ∧
  ⌜tm_assign0_m⌝ₚ(⌜ω⌝ₛ, ⌜Z⌝ₛ, A, ⌜e⌝ₛ, ⌜ν⌝ₛ, ⌜E⌝ₛ, ⌜n⌝ₛ, h) ∧
  ⌜tf_lower_type_m⌝ₚ(⌜ω⌝ₛ, ⌜C⌝ₛ, ⌜κ⌝ₛ, ⌜n⌝ₛ, A, h, ⌜δ⌝ₛ, ⌜t⌝ₛ)⟫
derive_free_closed tm_type_m

/-- 第零坐标为移动高度，其余十个坐标为共同参数。 -/
def tm_type_f : Formula 1 11 := tm_type_m (.bound 1) (.bound 2) (.bound 3) (.bound 4)
  (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) .newest (.bound 10)

theorem tm_type_closed_l : tm_type_f.FreeClosed := by
  apply tm_type_m_freeClosed <;> rfl

variable (hZF : M.Models ZF) {ω η Y : M.Domain} (hω : M.IsOmega ω)
  (hη : M.IsLimitOrdinal η) (hY : V_d (kp_pair_l (ZF.modelsKP hZF)) η Y) (hωY : M.mem ω Y)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)
local notation "T" => v_transitive_l Q hY
local notation "ny" => Nonempty.intro (Subtype.mk ω hωY)
local notation "N" => rt_model_l Y ny
local notation "J" => rt_pair_l T ny (And.left hZF) (sc_v_pair_l (ZF.modelsKP hZF) hη hY)
local notation "L" => fp_rank_interpretation_l Q hZF hω hY hωY

include hω hη hY in
theorem tm_type_source_l (C κ k n Z E δ e ν t : (N).Domain) {ξ β A B U D c R s : M.Domain}
    (hν : M.IsOrdinal ν.val) (hk : M.mem k.val ω)
    (sum : M.IsOrdinalAddition Q β ν.val k.val) (hβ : M.mem β η)
    (hA : V_d Q β A) (hων : M.MemberSubset ω β) (hκA : M.mem κ.val A)
    (hC : V_d Q ξ C.val) (hξ : M.IsLimitOrdinal ξ) (hωξ : M.mem ω ξ) (hκξ : M.mem κ.val ξ)
    (hB : V_d Q κ.val B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ.val)
    (pool : Tt_pool_d Q ω n.val U D) (hm : Smem_d Q c A R) (hn : M.mem n.val ω)
    (names : Fn0_d n.val Z.val E.val) (assign : Tn_assign_d e.val e.val ν.val E.val s)
    (tuple : Fn0_d n.val A s) (point : M.mem δ.val A) :
    Formula.satisfies (⟨Fin.cases ν (Fin.cases ⟨ω, hωY⟩ (Fin.cases C (Fin.cases κ (Fin.cases k
      (Fin.cases n (Fin.cases Z (Fin.cases E (Fin.cases δ (Fin.cases e (fun _ => t)))))))))), fun _ => ν⟩ : Env N 11)
      tm_type_f ↔ Tt_truth_d Q ω c n.val s δ.val D t.val := by
  let ρ : Env N 11 := ⟨Fin.cases ν (Fin.cases ⟨ω, hωY⟩ (Fin.cases C (Fin.cases κ (Fin.cases k
    (Fin.cases n (Fin.cases Z (Fin.cases E (Fin.cases δ (Fin.cases e (fun _ => t)))))))))), fun _ => ν⟩
  have ext := rt_model_ext_l hZF.1 T ny
  have add (b : (N).Domain) : (N).IsOrdinalAddition J b ν k ↔ b.val = β := by
    obtain ⟨a, _, unique⟩ := ZF.ordinalAddition_existsUnique hZF Q ν.val (hω.members_areOrdinals (ZF.modelsKP hZF) k.val hk)
    exact (rt_oa_l hZF hη hY ny ν k b hν).trans
      ⟨fun hb => (unique b.val hb).trans (unique β sum).symm, fun eq => eq.symm ▸ sum⟩
  have layer (b V : (N).Domain) (eq : b.val = β) : V_d L b V ↔ V.val = A :=
    (rt_fp_v_l Q hZF hω hY hωY b V).trans
      ⟨fun hv => ZF.v_unique_l Q hZF (eq ▸ hv) hA, fun ev => ev.symm ▸ eq.symm ▸ hA⟩
  have fn := rt_fp_function_from_l Q hZF hω hY hωY
  have mat (b V h : (N).Domain) : Formula.satisfies (((ρ.push b).push V).push h)
      (tm_assign0_m (.bound 4) (.bound 9) (.bound 1) (.bound 12) (.bound 3) (.bound 10) (.bound 8) .newest) ↔
      Tm_assign_d K Z.val V.val e.val ν.val E.val n.val h.val :=
    (rt_model_delta_l T ny (tm_assign0_delta_l ..) _).trans
      (tm_assign0_sat_l (ZF.models_kpi_l hZF) _ (.bound 4) (.bound 9) (.bound 1)
        (.bound 12) (.bound 3) (.bound 10) (.bound 8) .newest hω)
  have query (b V h : (N).Domain) (eq : V.val = A) (agree : Sx_graph_d Q K s h.val) :=
    tf_lower_type_source_l hZF hω hY hωY (((ρ.push b).push V).push h)
      (.bound 4) (.bound 5) (.bound 6) (.bound 8) (.bound 1) .newest (.bound 11) (.bound 13) rfl
      hC hξ hωξ hκξ (eq.symm ▸ hA) hων (eq.symm ▸ hκA) hB constants pool
      (eq.symm ▸ hm) hn (eq.symm ▸ tuple) (eq.symm ▸ point) agree
  change Formula.satisfies ρ tm_type_f ↔ _
  simp only [tm_type_f, tm_type_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isOrdinalAddition_iff J ext, v_sat_l L ext,
    Formula.satisfies_isFunctionFromTo_iff L ext, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨b, V, h, hb, hv, hh, matrix, truth⟩
    have eq := (layer b V ((add b).mp hb)).mp hv
    have flat := eq ▸ (fn h n V).mp hh
    have agree := (tm_assign_iff_l hZF names assign tuple flat).mp (eq ▸ (mat b V h).mp matrix)
    exact (query b V h eq agree).mp truth
  · intro truth
    let b : (N).Domain := ⟨β, ZF.v_ordinal_mem_l Q hZF hY hβ⟩
    let V : (N).Domain := ⟨A, ZF.v_mem_l Q hZF hA hY hβ⟩
    obtain ⟨h, flat, agree⟩ := fn_recode_l Q K hZF (fn0_function_l (ZF.modelsKP hZF) tuple)
    have hhY := v_subset_mem_l Q hY V.property
      (fp_function_rank_l Q hZF hω hA hων (fun i hi => ZF.v_ordinal_mem_l Q hZF hA (hων i (hω.transitive (ZF.modelsKP hZF) _ hn i hi))) flat)
    let h' : (N).Domain := ⟨h, hhY⟩
    exact ⟨b, V, h', (add b).mpr rfl, (layer b V rfl).mpr rfl, (fn h' n V).mpr flat,
      (mat b V h').mpr ((tm_assign_iff_l hZF names assign tuple flat).mpr agree), (query b V h' rfl agree).mpr truth⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 用指定点的完整类型读取移动后的较低类型 -/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u

def tm_params_l {α : Type u} (ω C κ k n Z E δ e t : α) : Fin 10 → α :=
  Fin.cases ω (Fin.cases C (Fin.cases κ (Fin.cases k (Fin.cases n
    (Fin.cases Z (Fin.cases E (Fin.cases δ (Fin.cases e (fun _ => t)))))))))

variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)

/-- 全部低参数只出现一次；指定高度 ν 是唯一随实现移动的坐标。 -/
theorem Tt_realized_d.move_read_l {ω e ν W F u c X R η C κ k n Z E δ t ξ β A B U D d S s : M.Domain}
    (l : Tt_realized_d Q ω c X R e e ν W F u) (model : Smem_d Q c X R)
    (hω : M.IsOmega ω) (hη : M.IsLimitOrdinal η) (hX : V_d Q η X)
    (hν : M.IsOrdinal ν) (hk : M.mem k ω) (sum : M.IsOrdinalAddition Q β ν k) (hβ : M.mem β η)
    (hA : V_d Q β A) (hων : M.MemberSubset ω β) (hκA : M.mem κ A)
    (hC : V_d Q ξ C) (hξ : M.IsLimitOrdinal ξ) (hωξ : M.mem ω ξ) (hκξ : M.mem κ ξ)
    (hB : V_d Q κ B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ)
    (pool : Tt_pool_d Q ω n U D) (hm : Smem_d Q d A S) (hn : M.mem n ω)
    (names : Fn0_d n Z E) (assign : Tn_assign_d e e ν E s) (tuple : Fn0_d n A s) (point : M.mem δ A)
    (ha : ∀ i, M.mem (tm_params_l ω C κ k n Z E δ e t i) W) :
    Formula.satisfies (l.point_env_l Q (tm_params_l ω C κ k n Z E δ e t) ha) tm_type_f ↔
      Tt_truth_d Q ω d n s δ D t := by
  have hwX := l.constants ω (ha 0)
  let ny : Nonempty {x // M.mem x X} := ⟨⟨ω, hwX⟩⟩
  let a (i : Fin 10) : (rt_model_l X ny).Domain :=
    ⟨tm_params_l ω C κ k n Z E δ e t i, l.constants _ (ha i)⟩
  let v : (rt_model_l X ny).Domain := ⟨ν, l.point⟩
  let ρ : Env (rt_model_l X ny) 11 := ⟨Fin.cases v a, fun _ => v⟩
  have read := tm_type_source_l hZF hω hη hX hwX (a 1) (a 2) (a 3) (a 4) (a 5)
    (a 6) (a 7) (a 8) v (a 9) hν hk sum hβ hA hων hκA hC hξ hωξ hκξ hB constants pool
    hm hn names assign tuple point
  have env : (⟨Fin.cases v (Fin.cases ⟨ω, hwX⟩ (Fin.cases (a 1) (Fin.cases (a 2)
      (Fin.cases (a 3) (Fin.cases (a 4) (Fin.cases (a 5) (Fin.cases (a 6)
        (Fin.cases (a 7) (Fin.cases (a 8) (fun _ => a 9)))))))))), fun _ => v⟩ : Env (rt_model_l X ny) 11).bound = ρ.bound := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))))))) i
  have result : Formula.satisfies ρ tm_type_f ↔ Tt_truth_d Q ω d n s δ D t :=
    (Formula.closed_env_l tm_type_f tm_type_closed_l env.symm).trans read
  exact (smem_formula_l Q model ny tm_type_f ρ).symm.trans result

end YesMetaZFC.SetTheory.Internal
