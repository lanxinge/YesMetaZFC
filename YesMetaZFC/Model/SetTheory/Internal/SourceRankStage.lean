import YesMetaZFC.Model.SetTheory.Internal.SourceHierarchy
import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource

/-! # 原秩历史的实际前缀与极限层展开

在所属源中限制原历史函数，得到同一较早层的相对秩证书。极限层中的每个
对象随后进入某个严格较早层；没有另选背景中的完整幂集层。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_rank_stage_l {ω c X R α V B F β W : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hV : M.mem V X) (hB : M.mem B X) (hF : M.mem F X)
    (cert : ∀ t, M.mem t X → Vc_d α V B F t) (hβ : M.mem β α) (hW : Rd_entry_d β W F) : Vr_d X β W := by
  have ho := (cert V hV).1
  have fn := (cert V hV).2.1
  have hβX := (rd_entry_transitive_l hX hF hW).1
  let ρ : Env M 1 := ⟨fun _ => F, fun _ => F⟩
  let φ : BinarySchema 1 := { body := rd_entry0_m (.bound 1) .newest (.bound 2) }
  have sat a b : φ.denote ρ a b ↔ Rd_entry_d a b F := rd_entry0_sat_l hZF.1 ..
  obtain ⟨G, hG, gf, select⟩ := sc_uniform_source_l hZF hω hX hm theory φ (rd_entry0_delta_l ..)
    ρ (fun _ => hF) hβX hB (fun a ha => (fn.2.1 a (ho.transitive β hβ a ha)).imp fun b hb => ⟨hb.1, (sat a b).mpr hb.2⟩)
  have edge a (ha : M.mem a β) b : Rd_entry_d a b G ↔ Rd_entry_d a b F := by
    refine ⟨fun h => (sat a b).mp (select a b h), fun h => ?_⟩
    obtain ⟨v, _, hav⟩ := gf.2.1 a ha
    exact (fn0_function_l (ZF.modelsKP hZF) fn).1.2 a v b ((sat a v).mp (select a v hav)) h ▸ hav
  have step δ (sub : M.MemberSubset δ β) U t : Vc_step_d δ B F U t ↔ Vc_step_d δ B G U t :=
    iff_congr Iff.rfl (exists_congr fun γ => and_congr_right fun hγ => exists_congr fun T =>
      and_congr_right fun _ => and_congr (edge γ (sub γ hγ) T).symm Iff.rfl)
  refine ⟨B, G, hB, hG, fun t ht => ⟨ho.mem hβ, gf, ?_, ?_⟩⟩
  · intro δ hδ U hu hg
    exact (step δ ((ho.mem hβ).transitive δ hδ) U t).mp
      ((cert t ht).2.2.1 δ (ho.transitive β hβ δ hδ) U hu ((edge δ hδ U).mp hg))
  · exact (step β (fun _ h => h) W t).mp ((cert t ht).2.2.1 β hβ W (fn.bound_l hW).2 hW)

theorem sc_rank_limit_l {ω c X R L V x : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hV : M.mem V X) (rank : Vr_d X L V) (limit : M.IsLimitOrdinal L) (hx : M.mem x V) :
    ∃ β W, M.mem β L ∧ M.mem W X ∧ Vr_d X β W ∧ M.mem x W := by
  obtain ⟨B, F, hB, hF, cert⟩ := rank
  have hxX := hX V hV x hx
  obtain ⟨α, hα, U, hU, hu, sub⟩ := ((cert x hxX).2.2.2).mp hx
  obtain ⟨β, hβ, hαβ⟩ := limit.2.2 α hα
  obtain ⟨W, hW, hw⟩ := (cert V hV).2.1.2.1 β hβ
  exact ⟨β, W, hβ, hX B hB W hW, sc_rank_stage_l hZF hω hX hm theory hV hB hF cert hβ hw,
    ((cert x hxX).2.2.1 β hβ W hW hw).mpr ⟨α, hαβ, U, hU, hu, sub⟩⟩

end YesMetaZFC.SetTheory.Internal
