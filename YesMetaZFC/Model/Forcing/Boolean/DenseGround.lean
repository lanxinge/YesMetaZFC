import YesMetaZFC.Model.Forcing.Boolean.DenseExtension
import YesMetaZFC.Model.Forcing.Stage.NameMap.Check
import YesMetaZFC.Model.Forcing.Ground.Collapse

/-! # 稠密图诱导的同构保持地模型

规范名称的基标签沿实际函数图搬运。共同加强消去基条件的选择，
从而原有稠密扩张同构与两侧规范嵌入交换。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u
variable {M : Structure.{u}} {P R z Q S w F : M.Domain}

theorem Reg_map_d.dense_ground_l (h : Reg_map_d M P R z Q S w F) (hZF : M.Models ZF)
    (O : Cond_order_d M P R z) (L : Cond_order_d M Q S w)
    (functional : ∀ p q r, Entry_d M p q F → Entry_d M p r F → q = r)
    {V : M.Domain → Prop} (generic : Generic_d M Q S w V) {b} (hb : V b)
    (dense : ∀ q, Below_d M Q S w q b → ∃ p r, Entry_d M p r F ∧ Entry_d M r q S) :
    Miso_over_d (Internal.extension_l M hZF P R z (Pull_generic_d M F V)) (Internal.extension_l M hZF Q S w V)
      (Gval_d M P R z (Pull_generic_d M F V)) (Gval_d M Q S w V) := by
  obtain ⟨f,values,mem,inj,onto⟩ := h.dense_extension_l hZF O L generic hb dense
  have source := reg_generic_l O L hZF h generic (h.dense_hit_l hZF L generic hb dense)
  have over x a (ha : Gval_d M P R z (Pull_generic_d M F V) x a) :
      Gval_d M Q S w V x (f a) := by
    obtain ⟨p,s,⟨q,pq,hq⟩,hs,sa⟩ := ha
    obtain ⟨t,ht,_,_⟩ := zf_check_l M hZF (generic.proper q hq).1 x
    have mapped := nmap_check_l hZF
      (fun r => ⟨fun pr => functional p r q pr pq,fun eq => eq.symm ▸ pq⟩) hs ht
    exact ⟨q,t,hq,ht,values a s t sa mapped⟩
  refine ⟨f,mem,inj,onto,fun x a => ⟨over x a,fun ha => ?_⟩⟩
  obtain ⟨d,hd⟩ := gval_exists_l hZF source x
  exact inj ((over x d hd).unique_l L hZF generic ha) ▸ hd

theorem Dmap_d.ground_l (h : Dmap_d P R z Q S w F) (hZF : M.Models ZF)
    (O : Cond_order_d M P R z) (L : Cond_order_d M Q S w)
    {V : M.Domain → Prop} (generic : Generic_d M Q S w V) :
    Miso_over_d (Internal.extension_l M hZF P R z (Pull_generic_d M F V)) (Internal.extension_l M hZF Q S w V)
      (Gval_d M P R z (Pull_generic_d M F V)) (Gval_d M Q S w V) := by
  obtain ⟨b,hb⟩ := generic.inhabited
  exact (h.regular_l L).dense_ground_l hZF O L h.functional generic hb
    (fun q hq => h.dense q hq.1 hq.2.1)

end YesMetaZFC.Model.Forcing.Internal
