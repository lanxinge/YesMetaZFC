import YesMetaZFC.SetTheory.InnerModel.OD.Syntax
import YesMetaZFC.Model.SetTheory.Internal.FiniteSource
import YesMetaZFC.Model.SetTheory.LevyReflection
import YesMetaZFC.SetTheory.Card.FiniteParameters

/-! # 内部 OD 与原公式唯一可定义性的等价

正向以有限反射把原定义送入一个实际 V 层，再统一编译全部候选值。反向使用
同一条标准解码公式，只需三个序数参数；即使内部公式和参数长度非标准亦成立。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project Internal
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 宿主有限原公式、有限个模型内序数参数的通常唯一可定义性。 -/
def Od_ext_d (x : M.Domain) : Prop := ∃ d, ∃ φ : UnarySchema d, ∃ ρ : Env M d,
  (∀ i, M.IsOrdinal (ρ.bound i)) ∧ ∀ y, φ.denote ρ y ↔ y = x

/-- 反射与内部编译实际生成定义码；不要求背景模型传递或 ω 标准。 -/
theorem od_source_l (hZF : M.Models ZF) {d} (φ : UnarySchema d) (ρ : Env M d)
    (hρ : ∀ i, M.IsOrdinal (ρ.bound i)) {x} (hx : ∀ y, φ.denote ρ y ↔ y = x) : Od_in_d I x := by
  -- 有限参数与空集组成序数字母表；编译取得的同一参数列供全部候选值使用。
  obtain ⟨ω, hω⟩ := ZF.exists_omega hZF
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  obtain ⟨B, _, hB⟩ := ZF.finite_params_l I hZF hω (Fin.cases e ρ.bound)
  have heB : M.mem e B := (hB e).mpr ⟨0, rfl⟩
  have hpB i : M.mem (ρ.bound i) B := (hB _).mpr ⟨i.succ, rfl⟩
  have hBo b (hb : M.mem b B) : M.IsOrdinal b := by
    obtain ⟨i, rfl⟩ := (hB b).mp hb
    exact Fin.cases (Structure.IsOrdinal.of_no_members he) hρ i
  obtain ⟨a, n, s, ⟨m, F, k, ha⟩, hn, hs, hc⟩ :=
    source_finite_compile_l I hZF hω he heB φ.body φ.freeClosed ρ.bound hpB
  obtain ⟨p, hp⟩ := oc_seq_exists_l I hZF hn
    ⟨⟨hω.members_areOrdinals hZF n hn, hs.1, hs.2.1⟩,
      fun _ _ b hb => hBo b (hs.output_mem_of_pairMember hb)⟩
  obtain ⟨z, hz⟩ := sc_num_exists_l I hZF hω ha
  -- 只反射给定的原公式；同层的全部参数赋值均保持其真值。
  obtain ⟨A, hA⟩ := KP.exists_insert (ZF.modelsKP hZF) B x
  obtain ⟨θ, X, hX, hAX, hr⟩ := ZF.lr_reflect_l I hZF φ.body φ.freeClosed A
  have ht := ZF.v_transitive_l I hZF hX
  have hBX : M.MemberSubset B X := fun b hb => ht A hAX b ((hA b).mpr (Or.inl hb))
  have hxX : M.mem x X := ht A hAX x ((hA x).mpr (Or.inr rfl))
  obtain ⟨c, R, hM, hR⟩ := smdl_membership_l I hZF ⟨e, hBX e heB⟩
  let η : Env (smdl_structure_l I (R := R) hM.2.1) d :=
    ⟨fun i => ⟨ρ.bound i, hBX _ (hpB i)⟩, fun _ => ⟨e, hBX e heB⟩⟩
  -- 编译、结构解码与反射复合，将背景的唯一性传入该层。
  have decode y : Ssk_mem_d I ω X e a e s y ↔ M.mem y X ∧ φ.denote ρ y := by
    rw [ssk_mem_decode_l I hZF.1 ⟨hM, hR⟩]
    apply and_congr_right
    intro hy
    exact (hc X c R hM hBX η (fun _ => rfl) ⟨y, hy⟩).trans
      (lr_model_l I hM hR ht φ.body φ.freeClosed hr (ρ.push y) (η.push ⟨y, hy⟩)
        (Fin.cases rfl (fun _ => rfl))).symm
  exact ⟨θ, z, p, ω, X, e, a, s, hω, hX, he, hBX e heB, hz, hp,
    (decode x).mpr ⟨hxX, (hx x).mpr rfl⟩, fun y hy => (hx y).mp ((decode y).mp hy).2⟩

/-- 固定标准解码公式；其参数依次是有限列码、公式码和层高度。 -/
def od_decoder_s (𝒞 : OrderedPairConvention) : UnarySchema 3 := {
  body := od_code_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 1) .newest }

/-- 非标准内部码也给出标准原公式定义，仅使用三个模型内序数参数。 -/
theorem od_code_external_l (hZF : M.Models ZF) {θ z p x} (h : Od_code_d I θ z p x) :
    ∃ ρ : Env M 3, (∀ i, M.IsOrdinal (ρ.bound i)) ∧
      ∀ y, (od_decoder_s 𝒞).denote ρ y ↔ y = x := by
  let ρ : Env M 3 := ⟨Fin.cases p (Fin.cases z (fun _ => θ)), fun _ => x⟩
  have ho := od_code_types_l I hZF h
  refine ⟨ρ, Fin.cases ho.2.2 (Fin.cases ho.2.1 (fun _ => ho.1)), fun y => ?_⟩
  have hd : (od_decoder_s 𝒞).denote ρ y ↔ Od_code_d I θ z p y := od_code_sat_l I hZF.1 _ _ _ _ _
  exact hd.trans ⟨fun hy => od_code_unique_l I hZF hy h, fun he => he.symm ▸ h⟩

theorem od_in_iff_external_l (hZF : M.Models ZF) {x} : Od_in_d I x ↔ Od_ext_d x := by
  constructor
  · rintro ⟨θ, z, p, h⟩
    obtain ⟨ρ, hρ, hd⟩ := od_code_external_l I hZF h
    exact ⟨3, od_decoder_s 𝒞, ρ, hρ, hd⟩
  · rintro ⟨d, φ, ρ, hρ, hx⟩
    exact od_source_l I hZF φ ρ hρ hx

/-- 有序对约定只改变表示，定义的 OD 类不变。 -/
theorem od_convention_l {𝒟 : OrderedPairConvention} (J : 𝒟.Interpretation M)
    (hZF : M.Models ZF) {x} : Od_in_d I x ↔ Od_in_d J x :=
  (od_in_iff_external_l I hZF).trans (od_in_iff_external_l J hZF).symm

end YesMetaZFC.SetTheory.InnerModel
