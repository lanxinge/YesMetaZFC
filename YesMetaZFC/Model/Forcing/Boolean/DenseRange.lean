import YesMetaZFC.Model.Forcing.Boolean.DenseMap
import YesMetaZFC.SetTheory.Card.OrdinalImage

/-! # 小稠密表示的实际小稠密像集

像集在原模型分离；按源条件的序数编号取最小原像，得到像集的实际单射界。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Dmap_d.small_range_l {P R z Q S w F κ : M.Domain} (h : Dmap_d P R z Q S w F)
    (fn : M.IsSetFunctionFromTo I F P Q) (hκ : M.IsOrdinal κ) (size : M.CardinalLessOrEqual I P κ) :
    ∃ E, (∀ x, M.mem x E ↔ ∃ p, M.mem p P ∧ Entry_d M p x F) ∧
      M.MemberSubset E Q ∧ M.CardinalLessOrEqual I E κ ∧
      ∀ q, M.mem q Q → q ≠ w → ∃ r, M.mem r E ∧ Below_d M Q S w r q := by
  let ρ : Env M 1 := ⟨fun _ => F,fun _ => F⟩
  let φ : UnarySchema 1 := { body := .existsE (entry_m .newest (.bound 1) (.bound 2)) }
  obtain ⟨E,members⟩ := ZF.separation_exists_d hZF φ ρ Q
  have image x : M.mem x E ↔ ∃ p, M.mem p P ∧ Entry_d M p x F := by
    apply (members x).trans
    have sat : φ.denote ρ x ↔ ∃ p, Entry_d M p x F := by
      simp only [UnarySchema.denote,φ,Formula.satisfies_exists_iff,entry_sat_l M hZF.1]; rfl
    apply (and_congr_right fun _ => sat).trans
    exact ⟨fun ⟨_,p,px⟩ => ⟨p,fn.input_mem_of_pairMember px,px⟩,
      fun ⟨p,_,px⟩ => ⟨fn.output_mem_of_pairMember px,p,px⟩⟩
  have sub : M.MemberSubset E Q := fun x hx => by
    obtain ⟨_,_,px⟩ := (image x).mp hx
    exact fn.output_mem_of_pairMember px
  have onto : M.IsSetSurjectiveOnto I F P E := fun x hx => (image x).mp hx
  have mapped : M.IsSetFunctionFromTo I F P E := ⟨fn.1,fn.2.1,fun p hp => by
    obtain ⟨x,_,px⟩ := fn.2.2 p hp
    exact ⟨x,(image x).mpr ⟨p,hp,px⟩,px⟩⟩
  refine ⟨E,image,sub,ZF.ordinal_image_bound_l I hZF hκ size mapped onto,?_⟩
  intro q hq nz
  obtain ⟨p,r,pr,rq⟩ := h.dense q hq nz
  exact ⟨r,(image r).mpr ⟨p,fn.input_mem_of_pairMember pr,pr⟩,
    (h.domain p r pr).2.1,(h.domain p r pr).2.2,rq⟩

end YesMetaZFC.Model.Forcing.Internal
