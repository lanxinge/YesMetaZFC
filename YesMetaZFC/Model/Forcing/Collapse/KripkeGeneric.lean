import YesMetaZFC.Model.Forcing.Collapse.KripkeMap
import YesMetaZFC.Model.Forcing.Collapse.PartialFunctionCertificate
import YesMetaZFC.Model.Forcing.Boolean.DensePush

/-! # 原泛型的 Kripke 坍缩呈示

在原泛型接受的条件下取实际稠密图，使用指定的有限序列偏序呈示回拉。
同一张图给出地参数保持的扩张同构，适用于有限前缀及小力迫乘大坍缩。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem kripke_generic_l {C S z a ω κ Q T : M.Domain} (O : Cond_order_d M C S z)
    (hw : M.IsOmega ω) (hκ : M.IsUncountableCardinal I ω κ) (size : M.CardinalLessOrEqual I C κ)
    (space : Fseq_space_d I ω κ Q) (L : Cond_order_d M Q T Q)
    (order : ∀ p q, Entry_d M p q T ↔ M.mem p Q ∧ M.mem q Q ∧ M.MemberSubset q p)
    {H : M.Domain → Prop} (generic : Generic_d M C S z H) (ha : H a) (collapse : Collapses_d C S z a ω κ) :
    ∃ Γ, Dmap_at_d Q T Q C S z Γ a ∧ Generic_d M Q T Q (Pull_generic_d M Γ H) ∧
      Miso_over_d (extension_l M hZF Q T Q (Pull_generic_d M Γ H)) (extension_l M hZF C S z H)
        (Gval_d M Q T Q (Pull_generic_d M Γ H)) (Gval_d M C S z H) := by
  have pos := generic.proper a ha
  obtain ⟨b,V,w,f,hb,ab,checkV,checkW,name⟩ := collapse.name_l hZFC O pos.1 pos.2
  obtain ⟨D,F,U,Γ,cone,_,sequences,sequenceOrder,_,map⟩ :=
    kripke_map_l hZFC O hw hκ size name hb ab checkV checkW
  have eq : F = Q := hZF.1.eq_of_same_members F Q (fun p => (sequences p).trans (space p).symm)
  subst F
  have same p q : Entry_d M p q U ↔ Entry_d M p q T := (sequenceOrder p q).trans (order p q).symm
  have map' : Dmap_d Q T Q D S z Γ := by
    refine ⟨map.total,map.domain,map.functional,?_,?_,map.dense⟩
    · intro p q x y px qy pq
      exact map.mono p q x y px qy ((same p q).mpr pq)
    · intro p q x y px qy compat
      obtain ⟨r,rp,rq⟩ := map.compat p q x y px qy compat
      exact ⟨r,⟨rp.1,rp.2.1,(same r p).mp rp.2.2⟩,(same r q).mp rq⟩
  have reg := map'.cone_regular_l O pos.1 cone
  have dense q (hq : Below_d M C S z q a) : ∃ p r, Entry_d M p r Γ ∧ Entry_d M r q S :=
    map'.dense q ((cone q).mpr hq) hq.2.1
  exact ⟨Γ,⟨reg,map'.functional,fun p q pq => (cone q).mp (map'.domain p q pq).2.1,dense⟩,
    reg_generic_l L O hZF reg generic (reg.dense_hit_l hZF O generic ha dense),
    reg.dense_ground_l hZF L O map'.functional generic ha dense⟩

end YesMetaZFC.Model.Forcing.Internal
