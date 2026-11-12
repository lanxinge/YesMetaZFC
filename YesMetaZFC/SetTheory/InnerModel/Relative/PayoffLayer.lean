import YesMetaZFC.SetTheory.InnerModel.Relative.TruthSyntax

/-! # 任意相对收益的共同 Jensen 层

对固定 `L[A]` 种子，把一个内部收益集和整个人类实数载体同时压入同一
个相对 Jensen 层。这个界是后续把 `La_d` 定义见证编译为双树时所需的
共同参数域，证明只使用已有的相对层界与传递性。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative

open Definitional.Project Descriptive
universe u
variable {M : Structure.{u}}

theorem la_payoff_layer_l
    (hZF : M.Models ZF)
    {ω B S : M.Domain} (seed : Lr_seed_d hZF ω B S)
    {A : (la_model_l S (ZF.models_kpi_l hZF)).Domain} :
    ∃ a U, Ja_d S a U ∧
      M.MemberSubset A.val U ∧ M.MemberSubset B U := by
  let hM := ZF.models_kpi_l hZF
  let hKP := ZF.modelsKP hZF
  obtain ⟨X, hX⟩ := KP.exists_unionOfTwo hKP A.val B
  have hmem : ∀ x, M.mem x X → La_d S x := by
    intro x hx
    rcases (hX x).mp hx with hxA | hxB
    · exact la_transitive_l S hM seed.2.1 A.property hxA
    · exact la_transitive_l S hM seed.2.1
        (lr_reals_in_seed_l hZF seed) hxB
  obtain ⟨a, U, hu, bound⟩ := la_bound_l S hM hmem
  refine ⟨a, U, hu, ?_, ?_⟩
  · intro x hx
    exact bound x ((hX x).mpr (Or.inl hx))
  · intro x hx
    exact bound x ((hX x).mpr (Or.inr hx))

def la_family_s : S1_binary 1 where
  matrix := {
    body := la0_m (.bound 3) (.bound 1) (.bound 2)
    delta0 := la0_delta_l .. }

/-! 同一收益集的所有成员还可由一次 Σ₁ 收集放入统一证书族。
后续树编码可在这个族上读取各点的 `La0_d` 递归见证。 -/
theorem la_payoff_witness_family_l
    (hZF : M.Models ZF)
    {ω B S : M.Domain} (seed : Lr_seed_d hZF ω B S)
    {A : (la_model_l S (ZF.models_kpi_l hZF)).Domain} :
    ∃ C, ∀ x, M.mem x A.val →
      ∃ T, M.mem T C ∧ La0_d S T x := by
  let hKP := ZF.modelsKP hZF
  obtain ⟨C, hC⟩ := KP.s1_collection_l hKP la_family_s (ja_env_l S) A.val (by
    intro x hx
    obtain ⟨T, ht⟩ := (la_witness_l S hKP.1 x).mp
      (la_transitive_l S (ZF.models_kpi_l hZF) seed.2.1 A.property hx)
    exact ⟨T, (S1_binary.sat_l la_family_s _ x T).mpr
      ⟨T, (la0_sat_l hKP _ _ _ _).mpr ht⟩⟩)
  refine ⟨C, ?_⟩
  intro x hx
  obtain ⟨T, hT, _, _, ht⟩ := hC x hx
  have hLa0 : La0_d S T x := by
    exact (la0_sat_l hKP _ _ _ _).mp ht
  exact ⟨T, hT, hLa0⟩

/-! 一旦递归证书载体保留其 Jensen 层归属，`La0_d` 中的全部对象就能
回收到同一个相对内模型。这个桥显式记录后续 producer 必须携带的最弱
层归属字段，不把它从 `Rc_cert_d` 虚构出来。 -/
theorem la0_layered_mem_l
    (hZF : M.Models ZF) (hS : M.TransitiveSet S)
    {T x : M.Domain} (h0 : La0_d S T x)
    (layer : ∃ a Y, Ja_d S a Y ∧ M.mem T Y) :
    La_d S T ∧ La_d S x := by
  let hM := ZF.models_kpi_l hZF
  obtain ⟨a, Y, hY, hTY⟩ := layer
  have hT : La_d S T := ⟨a, Y, hY, hTY⟩
  obtain ⟨a₀, Y₀, ha, hY₀, hₐ, hxY, A, F, hcert, haA, hYF⟩ := h0
  have hY₀' : La_d S Y₀ := la_transitive_l S hM hS hT hY₀
  exact ⟨hT, la_transitive_l S hM hS hY₀' hxY⟩

/-! 这是把递归证书族送入相对内模型所需的最小结构化证书。
`pool` 保证证书池本身属于某个 Jensen 层，`layer` 为每个成员保留同样的
层归属，`cover` 则保存收益成员的原始 `La0_d` 见证。 -/
def La0_layered_family_d (S A : M.Domain) : Prop :=
  ∃ C, (∃ a Y, Ja_d S a Y ∧ M.mem C Y) ∧
    (∀ x, M.mem x A → ∃ T, M.mem T C ∧ La0_d S T x) ∧
    (∀ T, M.mem T C → ∃ a Y, Ja_d S a Y ∧ M.mem T Y)

/-! 一个单独命名的层归属字段。把反复出现的 `∃ a Y, ...` 提升为可复用的
接口，后续证书生产器可以直接消费这个字段，而不必重新展开 Jensen 层定义。 -/
def La0_layer_mem_d (S T : M.Domain) : Prop :=
  ∃ a Y, Ja_d S a Y ∧ M.mem T Y

theorem la0_layer_mem_d_iff (S T : M.Domain) :
    La0_layer_mem_d S T ↔ ∃ a Y, Ja_d S a Y ∧ M.mem T Y := Iff.rfl

def la0_collection_s : BinarySchema 1 where
  body := la0_m (.bound 2) (.bound 0) (.bound 1)
  freeClosed := la0_m_freeClosed _ _ _ (by simp) (by simp) (by simp)

/-! 以下运输链把内模型中的递归证书逐项送回背景模型。证书检查和条目
关系都是 Δ₀，故只用相对模型的有界绝对性，不把 carrier 的层归属当作
`Rc_cert_d` 的隐藏字段。 -/
theorem la0_rc_cert_inner_outer_l
    (hZF : M.Models ZF) (hS : M.TransitiveSet S)
    {n} {φ : S1_binary n} {ρ : Env (la_model_l S (ZF.models_kpi_l hZF)) n}
    {A F T : (la_model_l S (ZF.models_kpi_l hZF)).Domain}
    (h : Rc_cert_d φ ρ A F T) :
    Rc_cert_d φ (image_env_l (M := la_model_l S (ZF.models_kpi_l hZF))
      (N := M) Subtype.val ρ) A.val F.val T.val := by
  let hM := ZF.models_kpi_l hZF
  let N := la_model_l S hM
  let hE := la_model_ext_l S hM hS
  let e : Fin n → Term (n + 3) := fun i => Term.bound ⟨i.val + 3, by omega⟩
  let η : Env N (n + 3) := ((ρ.push A).push F).push T
  have hρ : (⟨fun i => (e i).eval η, η.free⟩ : Env N n) = ρ := by
    rw [Env.mk.injEq]
    constructor
    · funext i
      simp [e, η, Env.push]
    · rfl
  have hi0 := (rc_cert_sat_l (M := N) hE φ η e (Term.bound 2) (Term.bound 1) (Term.bound 0))
  rw [hρ] at hi0
  have hi := hi0.mpr h
  have hd := la_model_delta_l S hM hS (rc_cert_delta_l φ e (Term.bound 2) (Term.bound 1) (Term.bound 0)) η
  have ho : Formula.satisfies (image_env_l (M := N) (N := M) Subtype.val η)
      (rc_cert_m φ e (Term.bound 2) (Term.bound 1) (Term.bound 0)) := hd.mp hi
  have ho' := (rc_cert_sat_l (M := M) hZF.1 φ (image_env_l (M := N) (N := M) Subtype.val η)
    (fun i => Term.bound ⟨i.val + 3, by omega⟩) (Term.bound 2) (Term.bound 1) (Term.bound 0)).mp ho
  have hρo :
      (⟨fun i => (Term.bound ⟨i.val + 3, by omega⟩).eval
        (image_env_l (M := N) (N := M) Subtype.val η),
        (image_env_l (M := N) (N := M) Subtype.val η).free⟩ : Env M n) =
        image_env_l (M := N) (N := M) Subtype.val ρ := by
    rw [Env.mk.injEq]
    constructor
    · funext i
      simp [η, image_env_l, Env.push]
    · rfl
  rw [hρo] at ho'
  have hAeval : (Term.bound (2 : Fin (n + 3))).eval
      (image_env_l (M := N) (N := M) Subtype.val η) = A.val := by rfl
  have hFeval : (Term.bound (1 : Fin (n + 3))).eval
      (image_env_l (M := N) (N := M) Subtype.val η) = F.val := by rfl
  have hTeval : (Term.bound (0 : Fin (n + 3))).eval
      (image_env_l (M := N) (N := M) Subtype.val η) = T.val := by rfl
  rw [hAeval, hFeval, hTeval] at ho'
  exact ho'

theorem la0_rd_entry_inner_outer_l
    (hZF : M.Models ZF) (hS : M.TransitiveSet S)
    {p a b : (la_model_l S (ZF.models_kpi_l hZF)).Domain} (h : Rd_entry_d p a b) :
    Rd_entry_d p.val a.val b.val := by
  let hM := ZF.models_kpi_l hZF
  let N := la_model_l S hM
  let hE := la_model_ext_l S hM hS
  let η : Env N 3 := ((⟨fun _ => p, fun _ => p⟩ : Env N 1).push a).push b
  have hi0 := (rd_entry0_sat_l (M := N) hE η (Term.bound 2) (Term.bound 1) (Term.bound 0))
  have hi : Formula.satisfies η (rd_entry0_m (Term.bound 2) (Term.bound 1) (Term.bound 0)) :=
    hi0.mpr (by simpa [η, Env.push, fin_cases] using h)
  have hd := la_model_delta_l S hM hS (rd_entry0_delta_l (Term.bound 2) (Term.bound 1) (Term.bound 0)) η
  have ho := hd.mp hi
  have hout := (rd_entry0_sat_l (M := M) hZF.1 (image_env_l (M := N) (N := M) Subtype.val η)
      (Term.bound 2) (Term.bound 1) (Term.bound 0)).mp ho
  simpa [η, image_env_l, Env.push, fin_cases] using hout

theorem la0_ja_value_inner_outer_l
    (hZF : M.Models ZF) (hS : M.TransitiveSet S)
    {a Y : (la_model_l S (ZF.models_kpi_l hZF)).Domain}
    (h : Ja_value_d (M := la_model_l S (ZF.models_kpi_l hZF))
      ⟨S, la_seed_l S (ZF.models_kpi_l hZF)⟩ a Y) :
    Ja_value_d (M := M) S a.val Y.val := by
  let hM := ZF.models_kpi_l hZF
  let N := la_model_l S hM
  let s : N.Domain := ⟨S, la_seed_l S hM⟩
  let hE := la_model_ext_l S hM hS
  have hv : Rc_value_d (M := N) ja_op_s (ja_env_l s) a Y :=
    (rc_value_sat_l (M := N) hE ja_op_s (ja_env_l s) a Y).mp h
  rcases hv with ⟨T, A, F, hcert, haA, hentry⟩
  have hcert' := la0_rc_cert_inner_outer_l hZF hS hcert
  have hentry' := la0_rd_entry_inner_outer_l hZF hS hentry
  have hv' : Rc_value_d (M := M) ja_op_s (ja_env_l S) a.val Y.val :=
    ⟨T.val, A.val, F.val, hcert', haA, hentry'⟩
  exact (rc_value_sat_l (M := M) hZF.1 ja_op_s (ja_env_l S) a.val Y.val).mpr hv'

theorem la0_ordinal_inner_l
    (hZF : M.Models ZF) (hS : M.TransitiveSet S) {a : M.Domain}
    (ha : M.IsOrdinal a) :
    (la_model_l S (ZF.models_kpi_l hZF)).IsOrdinal
      ⟨a, la_ordinal_l S (ZF.models_kpi_l hZF) hS ha⟩ := by
  let hM := ZF.models_kpi_l hZF
  let N := la_model_l S hM
  let a' : N.Domain := ⟨a, la_ordinal_l S hM hS ha⟩
  let η : Env N 1 := ⟨fun _ => a', fun _ => a'⟩
  have ho : Formula.satisfies (image_env_l (M := N) (N := M) Subtype.val η)
      (KP.ord0_m Term.newest) :=
    (KP.ord0_sat_l (ZF.modelsKP hZF) (image_env_l (M := N) (N := M) Subtype.val η)
      Term.newest).mpr (by
        change M.IsOrdinal a
        exact ha)
  have hi : Formula.satisfies η (KP.ord0_m Term.newest) :=
    (la_model_delta_l S hM hS (KP.ord0_delta_l Term.newest) η).mpr ho
  exact (KP.ord0_sat_l (ZF.modelsKP (la_model_zf_l S hZF hS)) η Term.newest).mp hi

theorem la0_inner_of_outer_l
    (hZF : M.Models ZF) (hS : M.TransitiveSet S) {x : M.Domain}
    (hx : La_d S x) :
    La_d (M := la_model_l S (ZF.models_kpi_l hZF))
      ⟨S, la_seed_l S (ZF.models_kpi_l hZF)⟩
      ⟨x, hx⟩ := by
  let hM := ZF.models_kpi_l hZF
  let N := la_model_l S hM
  let s : N.Domain := ⟨S, la_seed_l S hM⟩
  let hx0 := hx
  rcases hx with ⟨a, Y, ha, hxy⟩
  let a' : N.Domain := ⟨a, la_ordinal_l S hM hS ha.1⟩
  obtain ⟨Y', hY'⟩ := ja_value_exists_l (M := N) s
    (ZF.models_kpi_l (la_model_zf_l S hZF hS)) a'
  have hYout := la0_ja_value_inner_outer_l hZF hS hY'
  have heq : Y = Y'.val := ja_value_unique_l S hM ha.2 hYout
  have hmem : N.mem ⟨x, hx0⟩ Y' := by
    change M.mem x Y'.val
    rw [← heq]
    exact hxy
  refine ⟨a', Y', ⟨la0_ordinal_inner_l hZF hS ha.1, hY'⟩, hmem⟩

theorem la0_inner_outer_l
    (hZF : M.Models ZF) (hS : M.TransitiveSet S)
    {x y : (la_model_l S (ZF.models_kpi_l hZF)).Domain}
    (h : La0_d (M := la_model_l S (ZF.models_kpi_l hZF))
      ⟨S, la_seed_l S (ZF.models_kpi_l hZF)⟩ y x) :
    La0_d S y.val x.val := by
  let hM := ZF.models_kpi_l hZF
  let N := la_model_l S hM
  let s : N.Domain := ⟨S, la_seed_l S hM⟩
  let ρ : Env N 1 := ja_env_l s
  let η : Env N 3 := ((ρ.push x).push y)
  have hi := (la0_sat_l (M := N) (ZF.modelsKP (la_model_zf_l S hZF hS)) η
    (Term.bound 2) (Term.bound 0) (Term.bound 1)).mpr h
  have hd := la_model_delta_l S hM hS (la0_delta_l (Term.bound 2) (Term.bound 0) (Term.bound 1)) η
  have ho := hd.mp hi
  have hout := (la0_sat_l (M := M) (ZF.modelsKP hZF)
    (image_env_l (M := N) (N := M) Subtype.val η)
    (Term.bound 2) (Term.bound 0) (Term.bound 1)).mp ho
  change La0_d S y.val x.val at hout
  exact hout

/-! 收集定理的内部版本保留证书 carrier、函数图和层递归见证本身，
供后续把 `La0_d` 编译成树节点，而不是先退回外部谓词再丢失见证。 -/
theorem la0_internal_collection_l
    (hZF : M.Models ZF) (hS : M.TransitiveSet S)
    {A : (la_model_l S (ZF.models_kpi_l hZF)).Domain} :
    ∃ C : (la_model_l S (ZF.models_kpi_l hZF)).Domain,
      ∀ x, (la_model_l S (ZF.models_kpi_l hZF)).mem x A →
        ∃ T, (la_model_l S (ZF.models_kpi_l hZF)).mem T C ∧
          La0_d (M := la_model_l S (ZF.models_kpi_l hZF))
            ⟨S, la_seed_l S (ZF.models_kpi_l hZF)⟩ T x := by
  let hM := ZF.models_kpi_l hZF
  let N := la_model_l S hM
  let s : N.Domain := ⟨S, la_seed_l S hM⟩
  let ρ : Env N 1 := ja_env_l s
  obtain ⟨C, hC⟩ := la_full_collection_l S hZF hS la0_collection_s ρ A (by
    intro x hx
    obtain ⟨T, hT⟩ := la_witness_l (M := N) s (la_model_ext_l S hM hS) x |>.mp
      (la0_inner_of_outer_l hZF hS x.property)
    exact ⟨T, by
      simpa [la0_collection_s, BinarySchema.denote] using
        ((la0_sat_l (M := N) (ZF.modelsKP (la_model_zf_l S hZF hS))
          ((ρ.push x).push T) (.bound 2) (.bound 0) (.bound 1)).mpr hT)⟩)
  refine ⟨C, ?_⟩
  intro x hx
  obtain ⟨T, hTC, hT⟩ := hC x hx
  have hT' : La0_d (M := N) s T x := by
    apply (la0_sat_l (M := N) (ZF.modelsKP (la_model_zf_l S hZF hS))
      ((ρ.push x).push T) (.bound 2) (.bound 0) (.bound 1)).mp
    simpa [la0_collection_s, BinarySchema.denote] using hT
  exact ⟨T, hTC, hT'⟩

/-! 这里实际构造递归证书载体的 Jensen 层归属字段。证书池 `C` 本身是
相对内模型元素，故 `C.property` 给出一个层 `U`；相对 Jensen 层的传递性
再把每个 `T ∈ C` 送入同一个 `U`。 -/
theorem la0_internal_collection_with_layer_l
    (hZF : M.Models ZF) (hS : M.TransitiveSet S)
    {A : (la_model_l S (ZF.models_kpi_l hZF)).Domain} :
    ∃ C : (la_model_l S (ZF.models_kpi_l hZF)).Domain,
      ∀ x, (la_model_l S (ZF.models_kpi_l hZF)).mem x A →
        ∃ T, (la_model_l S (ZF.models_kpi_l hZF)).mem T C ∧
          La0_d (M := la_model_l S (ZF.models_kpi_l hZF))
            ⟨S, la_seed_l S (ZF.models_kpi_l hZF)⟩ T x ∧
          La0_layer_mem_d S T.val := by
  let hM := ZF.models_kpi_l hZF
  let N := la_model_l S hM
  obtain ⟨C, hC⟩ := la0_internal_collection_l hZF hS
  obtain ⟨a, U, hU, hCU⟩ := C.property
  refine ⟨C, ?_⟩
  intro x hx
  obtain ⟨T, hTC, hT⟩ := hC x hx
  have hTU : M.mem T.val U :=
    ja_transitive_l S hM hS hU.2 C.val hCU T.val hTC
  exact ⟨T, hTC, hT, ⟨a, U, hU, hTU⟩⟩

/-! 将池自身的层、覆盖见证和每个证书成员的层归属一次性导出。
这个出口保留内部 subtype 的真实证明字段，后续 producer 可以直接读取
`La0_layer_mem_d`，不必再次从 `C.property` 重建同一层。 -/
theorem la0_internal_layered_fields_l
    (hZF : M.Models ZF) (hS : M.TransitiveSet S)
    {A : (la_model_l S (ZF.models_kpi_l hZF)).Domain} :
    ∃ C : (la_model_l S (ZF.models_kpi_l hZF)).Domain,
      (∃ a Y, Ja_d (M := la_model_l S (ZF.models_kpi_l hZF))
        ⟨S, la_seed_l S (ZF.models_kpi_l hZF)⟩ a Y ∧
        (la_model_l S (ZF.models_kpi_l hZF)).mem C Y) ∧
      (∀ x, (la_model_l S (ZF.models_kpi_l hZF)).mem x A →
        ∃ T, (la_model_l S (ZF.models_kpi_l hZF)).mem T C ∧
          La0_d (M := la_model_l S (ZF.models_kpi_l hZF))
            ⟨S, la_seed_l S (ZF.models_kpi_l hZF)⟩ T x ∧
          La0_layer_mem_d S T.val) ∧
      (∀ T, (la_model_l S (ZF.models_kpi_l hZF)).mem T C →
        La0_layer_mem_d S T.val) := by
  let hM := ZF.models_kpi_l hZF
  let N := la_model_l S hM
  obtain ⟨C, cover⟩ := la0_internal_collection_with_layer_l (S := S) hZF hS
  obtain ⟨a₀, Y₀, hY₀, hCY₀⟩ := C.property
  obtain ⟨a, Y, hY, hCY⟩ := la0_inner_of_outer_l hZF hS C.property
  refine ⟨C, ⟨a, Y, hY, hCY⟩, cover, ?_⟩
  intro T hTC
  exact ⟨a₀, Y₀, hY₀, ja_transitive_l S hM hS hY₀.2 C.val hCY₀ T.val hTC⟩

/-! 层归属字段还可以一次性运输 `La0_d` 的所有有限证书坐标。这个输出
保留原始 `Rc_cert_d` 和 `Rd_entry_d`，所以后续树编码读取的是实际证书，
而不是由层归属反向猜出的占位关系。 -/
theorem la0_certificate_layer_fields_l
    (hZF : M.Models ZF) (hS : M.TransitiveSet S)
    {T x : M.Domain} (h0 : La0_d S T x)
    (layer : La0_layer_mem_d S T) :
    ∃ a Y A F U α,
      Ja_d S α U ∧ M.mem T U ∧
      M.mem a U ∧ M.mem Y U ∧ M.mem A U ∧ M.mem F U ∧ M.mem x U ∧
      M.IsOrdinal a ∧ M.mem a T ∧ M.mem Y T ∧ M.mem x Y ∧
      Rc_cert_d ja_op_s (ja_env_l S) A F T ∧ M.mem a A ∧ Rd_entry_d a Y F := by
  let hM := ZF.models_kpi_l hZF
  obtain ⟨α, U, hU, hTU⟩ := layer
  obtain ⟨a, Y, haT, hYT, ha, hxY, A, F, hcert, haA, hYF⟩ := h0
  have haU : M.mem a U := ja_transitive_l S hM hS hU.2 T hTU a haT
  have hYU : M.mem Y U := ja_transitive_l S hM hS hU.2 T hTU Y hYT
  have hAU : M.mem A U := ja_transitive_l S hM hS hU.2 T hTU A hcert.domain
  have hFU : M.mem F U := ja_transitive_l S hM hS hU.2 T hTU F hcert.graph
  have hxU : M.mem x U := ja_transitive_l S hM hS hU.2 Y hYU x hxY
  exact ⟨a, Y, A, F, U, α, hU, hTU, haU, hYU, hAU, hFU, hxU,
    ha, haT, hYT, hxY, hcert, haA, hYF⟩

/-! 内部收集的载体本身带有 `La_d` 证明，因此可以把该证明逐项运输到
证书成员上。这个定理把缺失的 Jensen 层归属字段显式构造出来，所有字段
都仍在相对内模型中，后续树生产器可直接读取而无需重新选择层号。 -/
theorem la0_internal_layered_family_l
    (hZF : M.Models ZF) (hS : M.TransitiveSet S)
    {A : (la_model_l S (ZF.models_kpi_l hZF)).Domain} :
    ∃ C : (la_model_l S (ZF.models_kpi_l hZF)).Domain,
      (∃ a Y, Ja_d (M := la_model_l S (ZF.models_kpi_l hZF))
        ⟨S, la_seed_l S (ZF.models_kpi_l hZF)⟩ a Y ∧
        (la_model_l S (ZF.models_kpi_l hZF)).mem C Y) ∧
      (∀ x, (la_model_l S (ZF.models_kpi_l hZF)).mem x A →
        ∃ T, (la_model_l S (ZF.models_kpi_l hZF)).mem T C ∧
          La0_d (M := la_model_l S (ZF.models_kpi_l hZF))
            ⟨S, la_seed_l S (ZF.models_kpi_l hZF)⟩ T x) ∧
      (∀ T, (la_model_l S (ZF.models_kpi_l hZF)).mem T C →
        ∃ a Y, Ja_d (M := la_model_l S (ZF.models_kpi_l hZF))
          ⟨S, la_seed_l S (ZF.models_kpi_l hZF)⟩ a Y ∧
          (la_model_l S (ZF.models_kpi_l hZF)).mem T Y) := by
  let hM := ZF.models_kpi_l hZF
  let N := la_model_l S hM
  let s : N.Domain := ⟨S, la_seed_l S hM⟩
  obtain ⟨C, hC⟩ := la0_internal_collection_l (S := S) hZF hS
  obtain ⟨a, Y, hY, hCY⟩ := la0_inner_of_outer_l (S := S) hZF hS C.property
  refine ⟨C, ⟨a, Y, hY, hCY⟩, hC, ?_⟩
  intro T hTC
  exact ⟨a, Y, hY, ja_transitive_l s
    (ZF.models_kpi_l (la_model_zf_l S hZF hS))
    (by
      intro x hx y hy
      exact hS x.val hx y.val hy)
    hY.2 C hCY T hTC⟩

/-! 内部收集的每个递归见证现在同时带有外部 Jensen 层中的完整证书
坐标。这个出口把内部 `La0_d` 运输到背景模型，再调用已构造的层字段，
因此后续树编码可以直接读取 `T`、其层 `U` 以及 `Rc_cert_d` 的实际图。 -/
theorem la0_internal_certificate_layered_fields_l
    (hZF : M.Models ZF) (hS : M.TransitiveSet S)
    {A : (la_model_l S (ZF.models_kpi_l hZF)).Domain} :
    ∃ C : (la_model_l S (ZF.models_kpi_l hZF)).Domain,
      ∀ x, (la_model_l S (ZF.models_kpi_l hZF)).mem x A →
        ∃ T, (la_model_l S (ZF.models_kpi_l hZF)).mem T C ∧
          La0_d (M := la_model_l S (ZF.models_kpi_l hZF))
            ⟨S, la_seed_l S (ZF.models_kpi_l hZF)⟩ T x ∧
          ∃ a Y A₀ F U α,
            Ja_d S α U ∧ M.mem T.val U ∧ M.mem a U ∧ M.mem Y U ∧
            M.mem A₀ U ∧ M.mem F U ∧ M.mem x.val U ∧
            M.IsOrdinal a ∧ M.mem a T.val ∧ M.mem Y T.val ∧
            M.mem x.val Y ∧ Rc_cert_d ja_op_s (ja_env_l S) A₀ F T.val ∧
            M.mem a A₀ ∧ Rd_entry_d a Y F := by
  let hM := ZF.models_kpi_l hZF
  let N := la_model_l S hM
  let s : N.Domain := ⟨S, la_seed_l S hM⟩
  obtain ⟨C, _, hCover, hLayerAll⟩ := la0_internal_layered_fields_l (S := S) hZF hS
  refine ⟨C, ?_⟩
  intro x hx
  obtain ⟨T, hTC, hT, hLayer⟩ := hCover x hx
  have hLayer' : La0_layer_mem_d S T.val := by
    exact hLayer
  have hOuter : La0_d S T.val x.val := la0_inner_outer_l hZF hS hT
  obtain ⟨a, Y, A₀, F, U, α, hU, hTU, haU, hYU, hA₀U, hFU, hxU,
      ha, haT, hYT, hxY, hcert, haA₀, hYF⟩ :=
    la0_certificate_layer_fields_l hZF hS hOuter hLayer'
  exact ⟨T, hTC, hT, a, Y, A₀, F, U, α, hU, hTU, haU, hYU, hA₀U, hFU,
    hxU, ha, haT, hYT, hxY, hcert, haA₀, hYF⟩

theorem la0_layered_family_l
    (hZF : M.Models ZF) (hS : M.TransitiveSet S)
    {A : (la_model_l S (ZF.models_kpi_l hZF)).Domain} :
    La0_layered_family_d S A.val := by
  let hM := ZF.models_kpi_l hZF
  let N := la_model_l S hM
  obtain ⟨C, hC⟩ := la0_internal_collection_l hZF hS
  obtain ⟨a, U, hU, hCU⟩ := C.property
  refine ⟨C.val, ⟨a, U, hU, hCU⟩, ?_, ?_⟩
  · intro x hx
    let x' : N.Domain := ⟨x, la_transitive_l S hM hS A.property hx⟩
    obtain ⟨T, hTC, hT⟩ := hC x' hx
    exact ⟨T.val, hTC, la0_inner_outer_l hZF hS hT⟩
  · intro T hTC
    exact ⟨a, U, hU, ja_transitive_l S hM hS hU.2 C.val hCU T hTC⟩

theorem La0_layered_family_d.of_common_layer_l
    {S A C U : M.Domain}
    (pool : ∃ a, Ja_d S a U ∧ M.mem C U)
    (cover : ∀ x, M.mem x A → ∃ T, M.mem T C ∧ La0_d S T x)
    (members : ∀ T, M.mem T C → M.mem T U) :
    La0_layered_family_d S A := by
  obtain ⟨a, hU, hCU⟩ := pool
  refine ⟨C, ⟨a, U, hU, hCU⟩, cover, ?_⟩
  intro T hT
  exact ⟨a, U, hU, members T hT⟩

theorem La0_layered_family_d.inner_l
    (hZF : M.Models ZF)
    {A : (la_model_l S (ZF.models_kpi_l hZF)).Domain}
    (family : La0_layered_family_d S A.val) :
    ∃ C : (la_model_l S (ZF.models_kpi_l hZF)).Domain,
      ∀ x, (la_model_l S (ZF.models_kpi_l hZF)).mem x A →
        ∃ T, (la_model_l S (ZF.models_kpi_l hZF)).mem T C ∧
          La0_d S T.val x.val := by
  let hM := ZF.models_kpi_l hZF
  obtain ⟨C, pool, cover, layer⟩ := family
  obtain ⟨a, Y, hY, hCY⟩ := pool
  let C' : (la_model_l S hM).Domain := ⟨C, ⟨a, Y, hY, hCY⟩⟩
  refine ⟨C', ?_⟩
  intro x hx
  obtain ⟨T, hTC, h0⟩ := cover x.val hx
  obtain ⟨b, V, hV, hTV⟩ := layer T hTC
  have hT : La_d S T := ⟨b, V, hV, hTV⟩
  let T' : (la_model_l S hM).Domain := ⟨T, hT⟩
  exact ⟨T', hTC, h0⟩

end YesMetaZFC.SetTheory.InnerModel.Relative
