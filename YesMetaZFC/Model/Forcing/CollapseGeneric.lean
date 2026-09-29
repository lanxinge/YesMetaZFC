import YesMetaZFC.Model.Forcing.NoNewReals
import YesMetaZFC.Model.Forcing.GenericFunction

/-! # 塌缩泛型函数的内部名称

每个条件中的有序对赋以该条件为权重，得到实际内部关系名称。
指定坐标稠密集保证全定义，指定值稠密集保证满射，滤子的共同加强保证单值。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SmallGraph
universe u
variable {M : SetTheory.Structure.{u}} {B R ω : M.Domain} {U : M.Domain → Prop}

variable (O : Cond_order_d M B R B) (hZFC : M.Models ZFC) (hU : Generic_d M B R B U)
local notation "E" => extension_l M (ZFC.models_zf_l hZFC) B R B U
variable {hEN : Extensional (extension_l M (ZFC.models_zf_l hZFC) B R B U)}
  {hPN : ∀ a b, ∃ p, Pair_d (extension_l M (ZFC.models_zf_l hZFC) B R B U) p a b}
include O hZFC hU hEN hPN

theorem collapse_surjection_l {X Y b} (hω : M.IsOmega ω) (hb : U b)
    (hB : ∀ p, M.mem p B ↔ Coll_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω X Y p)
    (hR : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ M.MemberSubset q p)
    (hX : ¬ M.CardinalLessOrEqual (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) X ω) (hY : ∃ y, M.mem y Y)
    (e : M.Domain → (E).Domain) (hi : Function.Injective e)
    (he : ∀ a y, (E).mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
    (hv : ∀ a t, Check_d M b a t → Qval_d M B R B U t (e a)) :
    ∃ F : (E).Domain, (E).IsSetFunctionFromTo (kpair_interpretation_l E hEN hPN) F (e X) (e Y) ∧
      (E).IsSetSurjectiveOnto (kpair_interpretation_l E hEN hPN) F (e X) (e Y) := by
  classical
  let hZF := ZFC.models_zf_l hZFC
  let J := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  have hp {p} (hp : U p) : Coll_d J ω X Y p := (hB p).mp (hU.proper p hp).1
  have hbelow {p q} (hq : Coll_d J ω X Y q) (hpp : M.mem p B) (hs : M.MemberSubset p q) :
      Below_d M B R B q p := by
    have hqB := (hB q).mpr hq
    exact ⟨hqB, fun heq => KP.mem_irrefl_d (ZF.modelsKP hZF) B (heq ▸ hqB), (hR q p).mpr ⟨hqB, hpp, hs⟩⟩
  obtain ⟨p₀, hp₀⟩ := hU.inhabited
  have input a (ha : M.mem a X) : ∃ p, U p ∧ ∃ c, Entry_d M a c p := by
    let φ : UnarySchema 1 := { body := .existsE (entry_m (.bound 2) .newest (.bound 1)) }
    let ρ : Env M 1 := ⟨fun _ => a, fun _ => a⟩
    have hφ p : φ.denote ρ p ↔ ∃ c, Entry_d M a c p := by
      simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, entry_sat_l M hZF.1]
      rfl
    apply generic_pick_l hZF hU ⟨1, φ, ρ, hφ⟩ hp₀
    intro p hpp
    by_cases hn : ∃ c, Entry_d M a c p
    · exact ⟨p, below_refl_l O hpp.1 hpp.2.1, hn⟩
    · obtain ⟨c, hc⟩ := hY
      obtain ⟨q, hq, hqp, hac⟩ := coll_extend_l J hZF hω ((hB p).mp hpp.1) ha hc hn
      exact ⟨q, hbelow hq hpp.1 hqp, c, hac⟩
  have output c (hc : M.mem c Y) : ∃ p, U p ∧ ∃ a, Entry_d M a c p := by
    let φ : UnarySchema 1 := { body := .existsE (entry_m .newest (.bound 2) (.bound 1)) }
    let ρ : Env M 1 := ⟨fun _ => c, fun _ => c⟩
    have hφ p : φ.denote ρ p ↔ ∃ a, Entry_d M a c p := by
      simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, entry_sat_l M hZF.1]
      rfl
    apply generic_pick_l hZF hU ⟨1, φ, ρ, hφ⟩ hp₀
    intro p hpp
    obtain ⟨a, ha, hn⟩ := coll_fresh_l J hZF ((hB p).mp hpp.1) hX
    obtain ⟨q, hq, hqp, hac⟩ := coll_extend_l J hZF hω ((hB p).mp hpp.1) ha hc hn
    exact ⟨q, hbelow hq hpp.1 hqp, a, hac⟩
  obtain ⟨F, hF, hf⟩ := generic_function_l (hEN := hEN) (hPN := hPN) O hZF hU hb
    (fun hp' => ⟨(hp hp').1, (hp hp').2.1⟩) (fun p q h => ((hR p q).mp h).2.2) input e hi he hv
  refine ⟨F, hF, ?_⟩
  intro y hy
  obtain ⟨c, hc, rfl⟩ := (he Y y).mp hy
  obtain ⟨p, hp', a, hac⟩ := output c hc
  exact ⟨e a, (image_member_l e hi he).mpr ((hp hp').2.1 a c hac).1,
    (hf (e a) (e c)).mpr ⟨p, hp', a, c, hac, rfl, rfl⟩⟩

end YesMetaZFC.Model.Forcing.Internal
