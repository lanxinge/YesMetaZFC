import YesMetaZFC.Model.Forcing.Proper.Elementary.RelationPreimage
import YesMetaZFC.Model.Forcing.Proper.Master.Basic

/-! # 实际序同构保持同一个 N 的主条件

将 N 中的目标稠密集沿图拉回，使用源主条件，再通过 N 内函数求值取回像条件。
共同加强同样沿图搬运。整个证明只需要 ZF 和双射对实际序关系的保持与反射。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem mstr_map_l {ω χ H c J d N K P R Q S F p q} (hω : M.IsOmega ω)
    (hχ : M.IsLimitOrdinal χ) (hH : H_d I χ H)
    (hJ : ∀ x y, M.PairMember I x y J ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d I c d H J N K) (hElem : Selem_d I ω c d)
    (hPN : M.mem P N) (hFN : M.mem F N) (hF : M.IsSetBijectionFromTo I F P Q)
    (hIso : ∀ a b x y, Entry_d M a x F → Entry_d M b y F → (Entry_d M x y S ↔ Entry_d M a b R))
    (hm : Mstr_d M P R P N p) (hpq : Entry_d M p q F) : Mstr_d M Q S Q N q := by
  have fn := hF.1.1
  have htr := ZF.h_transitive_l I hZF hH
  have nz {a X} (ha : M.mem a X) : a ≠ X := fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) X (he ▸ ha)
  refine ⟨fn.output_mem_of_pairMember hpq, nz (fn.output_mem_of_pairMember hpq), fun D hDN hD r hr => ?_⟩
  obtain ⟨E, hEN, hE⟩ := selem_rel_pull_l hZF hω hχ hH hJ hSub hElem hPN hFN hDN
  have hd : Dense_set_d M P R P E := by
    refine ⟨fun a ha => ⟨hE.1 a ha, nz (hE.1 a ha)⟩, fun a ha _ => ?_⟩
    obtain ⟨x, hx, hax⟩ := fn.2.2 a ha
    obtain ⟨y, hyx, hyD⟩ := hD.2 x hx (nz hx)
    obtain ⟨b, hb, hby⟩ := hF.2 y hyx.1
    exact ⟨b, ⟨hb, nz hb, (hIso b a y x hby hax).mp hyx.2.2⟩,
      (hE.2 b hb).mpr ⟨y, hby, hyD⟩⟩
  obtain ⟨a, ha, har⟩ := hF.2 r hr.1
  obtain ⟨b, hbE, hbN, k, hka, hkb⟩ := hm.2.2 E hEN hd a
    ⟨ha, nz ha, (hIso a p r q har hpq).mp hr.2.2⟩
  obtain ⟨y, hy, hby⟩ := fn.2.2 b (hE.1 b hbE)
  have hyN := selem_entry_value_l I hJ htr hZF hω hSub hElem hFN hbN fn.1.2 hby
  obtain ⟨y', hby', hy'D⟩ := (hE.2 b (hE.1 b hbE)).mp hbE
  have he := fn.1.2 b y' y hby' hby
  obtain ⟨w, hw, hkw⟩ := fn.2.2 k hka.1
  exact ⟨y, he ▸ hy'D, hyN, w, ⟨hw, nz hw, (hIso k a w r hkw har).mpr hka.2.2⟩,
    (hIso k b w y hkw hby).mpr hkb⟩

end YesMetaZFC.Model.Forcing.Internal
