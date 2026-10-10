import YesMetaZFC.SetTheory.CumulativeRelativeAlgebra
import YesMetaZFC.SetTheory.KP.Ordinal

/-! # 相对极限秩层中的有界关系闭包

直接读取原秩历史，先统一两个坐标界，再提高有限次层号。
只收纳源中已经存在的图和图族；不把相对幂集改成背景完整幂集。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

omit hZF in
theorem Vr_d.subset_mem_l {Z α V A B : M.Domain} (hZ : M.TransitiveSet Z) (hV : M.mem V Z)
    (hv : Vr_d Z α V) (hA : M.mem A V) (hB : M.mem B Z) (sub : M.MemberSubset B A) : M.mem B V := by
  obtain ⟨C, F, _, _, cert⟩ := hv
  obtain ⟨β, hβ, U, hU, hβU, haU⟩ := ((cert A (hZ V hV A hA)).2.2.2).mp hA
  exact ((cert B hB).2.2.2).mpr ⟨β, hβ, U, hU, hβU, fun x hx => haU x (sub x hx)⟩

omit hZF in
theorem Vr_d.joint_bound_l {Z α V A B : M.Domain} (hZ : M.TransitiveSet Z) (hV : M.mem V Z)
    (hv : Vr_d Z α V) (hA : M.mem A V) (hB : M.mem B V) :
    ∃ U, M.mem U V ∧ M.MemberSubset A U ∧ M.MemberSubset B U := by
  obtain ⟨C, F, hC, _, cert⟩ := hv
  have ho := (cert V hV).1
  have fn := (cert V hV).2.1
  obtain ⟨β, hβ, P, hP, hβP, haP⟩ := ((cert A (hZ V hV A hA)).2.2.2).mp hA
  obtain ⟨γ, hγ, Q, hQ, hγQ, hbQ⟩ := ((cert B (hZ V hV B hB)).2.2.2).mp hB
  have member δ U (hδ : M.mem δ α) (hu : Rd_entry_d δ U F) : M.mem U V :=
    ((cert U (hZ C hC U (fn.bound_l hu).2)).2.2.2).mpr ⟨δ, hδ, U, (fn.bound_l hu).2, hu, fun _ h => h⟩
  have mono δ ε U W (hδ : M.mem δ α) (hε : M.mem ε α) (hu : Rd_entry_d δ U F) (hw : Rd_entry_d ε W F)
      (sub : M.MemberSubset δ ε) : M.MemberSubset U W := by
    intro x hx
    have hxZ := hZ U (hZ C hC U (fn.bound_l hu).2) x hx
    obtain ⟨ξ, hξ, T, hT, hξT, hxT⟩ := ((cert x hxZ).2.2.1 δ hδ U (fn.bound_l hu).2 hu).mp hx
    exact ((cert x hxZ).2.2.1 ε hε W (fn.bound_l hw).2 hw).mpr ⟨ξ, sub ξ hξ, T, hT, hξT, hxT⟩
  rcases ho.wellOrder.linear.compare β hβ γ hγ with eq | lt | gt
  · exact ⟨Q, member γ Q hγ hγQ, fun x hx => mono β γ P Q hβ hγ hβP hγQ (fun t ht => (eq t).mp ht) x (haP x hx), hbQ⟩
  · exact ⟨Q, member γ Q hγ hγQ, fun x hx => mono β γ P Q hβ hγ hβP hγQ (ho.mem hγ |>.transitive β lt) x (haP x hx), hbQ⟩
  · exact ⟨P, member β P hβ hβP, haP, fun x hx => mono γ β Q P hγ hβ hγQ hβP (ho.mem hβ |>.transitive γ gt) x (hbQ x hx)⟩

omit hZF in
/-- 一个较早层同时容纳所有源内有界关系图。 -/
theorem Vr_d.relation_cover_l {Z α V A B : M.Domain} (hZ : M.TransitiveSet Z) (hV : M.mem V Z)
    (hv : Vr_d Z α V) (hα : M.IsLimitOrdinal α) (hA : M.mem A V) (hB : M.mem B V) :
    ∃ W, M.mem W V ∧ ∀ F, M.mem F Z →
      (∀ p, M.mem p F → ∃ x, M.mem x A ∧ ∃ y, M.mem y B ∧ KPair_d M p x y) → M.mem F W := by
  obtain ⟨U, hU, au, bu⟩ := hv.joint_bound_l hZ hV hA hB
  obtain ⟨C, G, hC, _, cert⟩ := hv
  have fn := (cert V hV).2.1
  obtain ⟨β, hβ, P, hP, hβP, up⟩ := ((cert U (hZ V hV U hU)).2.2.2).mp hU
  obtain ⟨γ, hγ, hβγ⟩ := hα.2.2 β hβ
  obtain ⟨δ, hδ, hγδ⟩ := hα.2.2 γ hγ
  obtain ⟨ε, hε, hδε⟩ := hα.2.2 δ hδ
  obtain ⟨Q, hQ, hγQ⟩ := fn.2.1 γ hγ
  obtain ⟨T, hT, hδT⟩ := fn.2.1 δ hδ
  obtain ⟨W, hW, hεW⟩ := fn.2.1 ε hε
  refine ⟨W, ((cert W (hZ C hC W hW)).2.2.2).mpr ⟨ε, hε, W, hW, hεW, fun _ h => h⟩, fun F hF bound => ?_⟩
  refine ((cert F hF).2.2.1 ε hε W hW hεW).mpr ⟨δ, hδε, T, hT, hδT, fun p hp => ?_⟩
  obtain ⟨x, hx, y, hy, s, t, hs, ht, pair⟩ := bound p hp
  have hpZ := hZ F hF p hp
  have hsZ := hZ p hpZ s ((pair s).mpr (Or.inl rfl))
  have htZ := hZ p hpZ t ((pair t).mpr (Or.inr rfl))
  have hsQ := ((cert s hsZ).2.2.1 γ hγ Q hQ hγQ).mpr ⟨β, hβγ, P, hP, hβP,
    fun z hz => (hs z).mp hz ▸ up x (au x hx)⟩
  have htQ := ((cert t htZ).2.2.1 γ hγ Q hQ hγQ).mpr ⟨β, hβγ, P, hP, hβP,
    fun z hz => ((ht z).mp hz).elim (fun eq => eq ▸ up x (au x hx)) (fun eq => eq ▸ up y (bu y hy))⟩
  exact ((cert p hpZ).2.2.1 δ hδ T hT hδT).mpr ⟨γ, hγδ, Q, hQ, hγQ,
    fun z hz => ((pair z).mp hz).elim (fun eq => eq ▸ hsQ) (fun eq => eq ▸ htQ)⟩

theorem Vr_d.relation_mem_l {Z α V A B F : M.Domain} (hZ : M.TransitiveSet Z) (hV : M.mem V Z)
    (hv : Vr_d Z α V) (hα : M.IsLimitOrdinal α) (hA : M.mem A V) (hB : M.mem B V) (hF : M.mem F Z)
    (bound : ∀ p, M.mem p F → ∃ x, M.mem x A ∧ ∃ y, M.mem y B ∧ KPair_d M p x y) : M.mem F V := by
  obtain ⟨W, hW, cover⟩ := hv.relation_cover_l hZ hV hα hA hB
  exact hv.transitive_l hZF hZ hV W hW F (cover F hF bound)

omit hZF in
theorem Vr_d.relations_mem_l {Z α V A B J : M.Domain} (hZ : M.TransitiveSet Z) (hV : M.mem V Z)
    (hv : Vr_d Z α V) (hα : M.IsLimitOrdinal α) (hA : M.mem A V) (hB : M.mem B V) (hJ : M.mem J Z)
    (bound : ∀ F, M.mem F J → ∀ p, M.mem p F → ∃ x, M.mem x A ∧ ∃ y, M.mem y B ∧ KPair_d M p x y) : M.mem J V := by
  obtain ⟨W, hW, cover⟩ := hv.relation_cover_l hZ hV hα hA hB
  exact hv.subset_mem_l hZ hV hW hJ (fun F hF => cover F (hZ J hJ F hF) (bound F hF))

/-- 原历史中的每层都有正确的序数高度；这里只使用模型内成员归纳。 -/
theorem Vr_d.ordinal_height_l {Z α V γ : M.Domain} (hZ : M.TransitiveSet Z) (hV : M.mem V Z)
    (hv : Vr_d Z α V) (hγ : M.IsOrdinal γ) (hγV : M.mem γ V) : M.mem γ α := by
  obtain ⟨B, F, hB, _, cert⟩ := hv
  have ho := (cert V hV).1
  have fn := (cert V hV).2.1
  have step β W (hb : M.IsOrdinal β) (hW : M.mem W Z)
      (eqn : ∀ t, M.mem t Z → Vc_step_d β B F W t)
      (ih : ∀ δ, M.mem δ β → ∀ U, Rd_entry_d δ U F → ∀ ξ, M.IsOrdinal ξ → M.mem ξ U → M.mem ξ δ) :
      ∀ ξ, M.IsOrdinal ξ → M.mem ξ W → M.mem ξ β := by
    intro ξ hx hxW
    obtain ⟨δ, hδ, U, _, hδU, xu⟩ := (eqn ξ (hZ W hW ξ hxW)).mp hxW
    exact ordinal_down_l (ZF.modelsKP hZF) hx hb (fun η hη => ih δ hδ U hδU η (hx.mem hη) (xu η hη)) hδ
  let ρ : Env M 2 := ⟨Fin.cases α (fun _ => F), fun _ => α⟩
  let φ : UnarySchema 2 := { body := .imp (.mem .newest (.bound 1)) (.forallE
    (.imp (rd_entry0_m (.bound 1) .newest (.bound 3)) (.forallE
      (.imp (.mem .newest (.bound 1)) (.imp (KP.ord0_m .newest) (.mem .newest (.bound 2))))))) }
  have sat β : φ.denote ρ β ↔ M.mem β α → ∀ W, Rd_entry_d β W F → ∀ ξ, M.mem ξ W → M.IsOrdinal ξ → M.mem ξ β := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_forall_iff, rd_entry0_sat_l hZF.1, KP.ord0_sat_l (ZF.modelsKP hZF)]; rfl
  have all β (hβ : M.mem β α) : ∀ W, Rd_entry_d β W F → ∀ ξ, M.IsOrdinal ξ → M.mem ξ W → M.mem ξ β := by
    have proof := ZF.mem_ind_l M hZF I φ ρ (fun δ ih => (sat δ).mpr (fun hδ W hd ξ hx hoξ =>
      step δ W (ho.mem hδ) (hZ B hB W (fn.bound_l hd).2)
        (fun t ht => (cert t ht).2.2.1 δ hδ W (fn.bound_l hd).2 hd)
        (fun η hη U he ν hn hv => (sat η).mp (ih η hη) (ho.transitive δ hδ η hη) U he ν hv hn) ξ hoξ hx)) β
    exact fun W hw ξ hx hv => (sat β).mp proof hβ W hw ξ hv hx
  exact step α V ho hV (fun t ht => (cert t ht).2.2.2) all γ hγ hγV

/-- 同一个实际秩段在不同传递模型中具有同一高度。 -/
theorem Vr_d.height_unique_l {X Y α β V : M.Domain}
    (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y) (hV : M.mem V X) (hV' : M.mem V Y)
    (h : Vr_d X α V) (g : Vr_d Y β V) : α = β := by
  have ho : M.IsOrdinal α := by obtain ⟨_, _, _, _, cert⟩ := h; exact (cert V hV).1
  have ho' : M.IsOrdinal β := by obtain ⟨_, _, _, _, cert⟩ := g; exact (cert V hV').1
  exact hZF.1.eq_of_same_members α β (fun γ =>
    ⟨fun hγ => g.ordinal_height_l hZF hY hV' (ho.mem hγ) (h.ordinal_subset_l hZF hX hV γ hγ),
      fun hγ => h.ordinal_height_l hZF hX hV (ho'.mem hγ) (g.ordinal_subset_l hZF hY hV' γ hγ)⟩)

/-- 并集不提高先前见证层；使用同一历史中已经证明的传递性。 -/
theorem Vr_d.union_mem_l {Z α V A U : M.Domain} (hZ : M.TransitiveSet Z) (hV : M.mem V Z)
    (hv : Vr_d Z α V) (hA : M.mem A V) (hU : M.mem U Z) (hu : M.IsUnionOf U A) : M.mem U V := by
  obtain ⟨B, F, hB, _, cert⟩ := hv
  obtain ⟨β, hβ, W, hW, hβW, aw⟩ := ((cert A (hZ V hV A hA)).2.2.2).mp hA
  have ht := (vc_transitive_l hZF hZ hV hB cert).2 β hβ W hβW
  exact ((cert U hU).2.2.2).mpr ⟨β, hβ, W, hW, hβW, fun x hx =>
    ((hu x).mp hx).elim fun y hy => ht y (aw y hy.1) x hy.2⟩

omit hZF in
/-- 源内已有的有界子集族属于相对极限层。 -/
theorem Vr_d.subsets_mem_l {Z α V A P : M.Domain} (hZ : M.TransitiveSet Z) (hV : M.mem V Z)
    (hv : Vr_d Z α V) (hα : M.IsLimitOrdinal α) (hA : M.mem A V) (hP : M.mem P Z)
    (bound : ∀ x, M.mem x P → M.MemberSubset x A) : M.mem P V := by
  obtain ⟨B, F, _, _, cert⟩ := hv
  obtain ⟨β, hβ, W, hW, hβW, aw⟩ := ((cert A (hZ V hV A hA)).2.2.2).mp hA
  obtain ⟨δ, hδ, hβδ⟩ := hα.2.2 β hβ
  obtain ⟨U, hU, hδU⟩ := (cert V hV).2.1.2.1 δ hδ
  exact ((cert P hP).2.2.2).mpr ⟨δ, hδ, U, hU, hδU, fun x hx =>
    ((cert x (hZ P hP x hx)).2.2.1 δ hδ U hU hδU).mpr
      ⟨β, hβδ, W, hW, hβW, fun y hy => aw y (bound x hx y hy)⟩⟩

end YesMetaZFC.SetTheory
