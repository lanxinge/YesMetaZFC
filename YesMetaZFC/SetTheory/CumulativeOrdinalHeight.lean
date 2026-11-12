import YesMetaZFC.SetTheory.CumulativeCertificate
import YesMetaZFC.SetTheory.CumulativeClosure
import YesMetaZFC.SetTheory.KP.TransitiveInduction

/-! # KP 中实际秩层内的序数高度

归纳只量化给定历史的层值和根秩层中的对象。每个子集步骤把序数
压到某个更早层号之下；不使用全域层级存在或无界分离。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP

theorem KP.v_ordinal_height_l {δ U κ : M.Domain}
    (rank : V_d I δ U) (ordinal : M.IsOrdinal κ) (member : M.mem κ U) : M.mem κ δ := by
  obtain ⟨B,F,cert⟩ := vc_complete_l hKP rank
  have height := v_ordinal_l I rank
  have trans := v_transitive_l I rank
  let ρ : Env M 3 := ⟨Fin.cases B (Fin.cases U (fun _ => F)),fun _ => δ⟩
  let φ : Delta0UnarySchema 3 := {
    body := Formula.forallMem (.bound 1) (Formula.forallMem (.bound 3)
      (.imp (rd_entry0_m (.bound 2) (.bound 1) (.bound 5))
        (.imp (KP.ord0_m .newest) (.imp (.mem .newest (.bound 1)) (.mem .newest (.bound 2))))))
    delta0 := .forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..)
      (.imp (KP.ord0_delta_l _) (.imp (.mem ..) (.mem ..))))) }
  have read β : φ.toUnarySchema.denote ρ β ↔
      ∀ W, M.mem W B → ∀ γ, M.mem γ U → Rd_entry_d β W F →
        M.IsOrdinal γ → M.mem γ W → M.mem γ β := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_forallMem_iff,Formula.satisfies_imp_iff,
      rd_entry0_sat_l hKP.1,KP.ord0_sat_l hKP,Formula.satisfies_mem_iff]
    rfl
  have all := KP.transitive_induction_l hKP height.transitive φ ρ (by
    intro β hβ ih
    apply (read β).mpr
    intro W hW γ hγ edge ord mem
    obtain ⟨η,hη,Z,hZ,value,sub⟩ := ((cert γ).2.2.1 β hβ W hW edge).mp mem
    have bound : M.MemberSubset γ η := fun x hx =>
      (read η).mp (ih η hη) Z hZ x (trans γ hγ x hx) value (ord.mem hx) (sub x hx)
    exact ordinal_down_l hKP ord (height.mem hβ) bound hη)
  obtain ⟨β,hβ,W,hW,edge,sub⟩ := (cert κ).2.2.2.mp member
  have bound : M.MemberSubset κ β := fun x hx =>
    (read β).mp (all β hβ) W hW x (trans κ member x hx) edge (ordinal.mem hx) (sub x hx)
  exact ordinal_down_l hKP ordinal height bound hβ

end YesMetaZFC.SetTheory
