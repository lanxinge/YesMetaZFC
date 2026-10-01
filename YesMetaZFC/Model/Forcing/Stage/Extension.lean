import YesMetaZFC.Model.Forcing.Stage.Atomic.Basic
import YesMetaZFC.Model.Forcing.Stage.Generic

/-! # 阶段泛型扩张之间的实际嵌入

目标泛型自动回拉为源泛型。名称搬运在两侧泛型商中给出成员满覆盖的单射，
其像是目标模型中的传递子结构；不假定外部良基或额外模型呈现。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u
variable {M : SetTheory.Structure.{u}} {P R z Q S w F : M.Domain} {V : M.Domain → Prop}
variable (O : Cond_order_d M P R z) (L : Cond_order_d M Q S w) (hZF : M.Models ZF)
variable (h : Reg_embed_d M P R z Q S w F) (hV : Generic_d M Q S w V)
include O L hZF h hV
local notation "G" => Pull_generic_d M F V
local notation "E" => extension_l M hZF P R z G
local notation "N" => extension_l M hZF Q S w V

/-- 名称搬运的两侧商类等号精确对应，包括反射方向。 -/
theorem stage_value_eq_l {x y s t} {a b : (E).Domain} {c d : (N).Domain}
    (hx : Qval_d M P R z G x a) (hy : Qval_d M P R z G y b)
    (hs : Nmap_d M F x s) (ht : Nmap_d M F y t)
    (hc : Qval_d M Q S w V s c) (hd : Qval_d M Q S w V t d) : a = b ↔ c = d := by
  have hG := reg_generic_l O L hZF h hV
  constructor
  · intro hab
    obtain ⟨p, ⟨q, hpq, hq⟩, he⟩ := (qval_eq_l O hZF hG hx hy).mpr hab
    exact (qval_eq_l L hZF hV hc hd).mp
      ⟨q, hq, nmap_eq_push_l O L hZF h (qval_name_l hx) (qval_name_l hy) hs ht hpq he⟩
  · intro hcd
    apply Classical.byContradiction
    intro hab
    obtain ⟨q, hq, he⟩ := (qval_eq_l L hZF hV hc hd).mpr hcd
    obtain ⟨p, hp, hn⟩ := (generic_decide_l O hZF hG (eq_force_defined_l M hZF.1 P R z x y)).elim
      (fun hh => False.elim (hab ((qval_eq_l O hZF hG hx hy).mp hh))) id
    obtain ⟨v, hpv, hv⟩ := hp
    have hn := (nmap_neg_eq_l O L hZF h (qval_name_l hx) (qval_name_l hy) hs ht hpv).mp hn
    obtain ⟨r, hr, hrv, hrq⟩ := hV.directed v q hv hq
    have hr' := hV.proper r hr
    exact hn r ⟨hr'.1, hr'.2, hrv⟩
      (eq_force_lower_l L hZF (qval_name_l hc) (qval_name_l hd) q r he.1 ⟨hr'.1, hr'.2, hrq⟩ he)

/-- 自动回拉泛型并装配成员满覆盖的阶段嵌入；选择仅位于 Prop 存在证明中。 -/
theorem stage_extension_l :
    ∃ e : (E).Domain → (N).Domain,
      (∀ a s t, Qval_d M P R z G s a → Nmap_d M F s t → Qval_d M Q S w V t (e a)) ∧
      (∀ a y, y ∈ e a ↔ ∃ c, c ∈ a ∧ e c = y) ∧ Function.Injective e := by
  have hG := reg_generic_l O L hZF h hV
  have hall (a : (E).Domain) : ∃ b : (N).Domain, ∃ s t,
      Qval_d M P R z G s a ∧ Nmap_d M F s t ∧ Qval_d M Q S w V t b := by
    obtain ⟨s, _, hs⟩ := value_name_l a
    obtain ⟨t, ht, htN, _⟩ := stage_nmap_l hZF h s
    obtain ⟨b, hb⟩ := name_value_l (R := S) (z := w) (U := V) htN
    exact ⟨b, s, t, hs, ht, hb⟩
  obtain ⟨e, he⟩ := Classical.axiomOfChoice hall
  have hv a s t (hs : Qval_d M P R z G s a) (ht : Nmap_d M F s t) : Qval_d M Q S w V t (e a) := by
    obtain ⟨u, v, hu, huv, hv⟩ := he a
    have htN := nmap_name_l M hZF (fun b c hc => (h.domain b c hc).2.2.1) ht
    obtain ⟨b, hb⟩ := name_value_l (R := S) (z := w) (U := V) htN
    have heq := (stage_value_eq_l O L hZF h hV hu hs huv ht hv hb).mp rfl
    exact heq.symm ▸ hb
  refine ⟨e, hv, ?_, ?_⟩
  · intro a y
    obtain ⟨s, t, hs, hst, ht⟩ := he a
    constructor
    · intro hy
      obtain ⟨u, b, hub, hb, huy⟩ := (qval_mem_l L hZF hV ht).mp hy
      obtain ⟨c, p, hcp, hcu, hpb⟩ :=
        (nmap_entry_l M hZF.1 (check_ind_l M hZF) (KP.exists_pair (ZF.modelsKP hZF)) hst u b).mp hub
      obtain ⟨x, hx⟩ := name_value_l (R := R) (z := z) (U := G) (name_entry_l M (qval_name_l hs) hcp).1
      exact ⟨x, (qval_mem_l O hZF hG hs).mpr ⟨c, p, hcp, ⟨b, hpb, hb⟩, hx⟩,
        qval_unique_l (hv x c u hx hcu) huy⟩
    · rintro ⟨c, hca, rfl⟩
      obtain ⟨u, p, hup, ⟨b, hpb, hb⟩, huc⟩ := (qval_mem_l O hZF hG hs).mp hca
      obtain ⟨v, huv⟩ := nmap_exists_l M hZF F u
      have hvb := (nmap_entry_l M hZF.1 (check_ind_l M hZF) (KP.exists_pair (ZF.modelsKP hZF)) hst v b).mpr
        ⟨u, p, hup, huv, hpb⟩
      exact (qval_mem_l L hZF hV ht).mpr ⟨v, b, hvb, hb, hv c u v huc huv⟩
  · intro a b hab
    obtain ⟨s, t, hs, hst, ht⟩ := he a
    obtain ⟨u, v, hu, huv, hv⟩ := he b
    exact (stage_value_eq_l O L hZF h hV hs hu hst huv ht hv).mpr hab

end YesMetaZFC.Model.Forcing.Internal
