import YesMetaZFC.Model.SetTheory.Internal.FiniteEmbedding
import YesMetaZFC.SetTheory.Descriptive.Prefix

/-! # 完整初等嵌入的有限尝试

节点按给定枚举的前若干项记录像。重复编号的一致性、规定的限制图和
全部内部公式的有限赋值真值共同决定节点；不是只检验原子嵌入。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def At_coherent_d (n A B e p : M.Domain) : Prop := ∀ i, M.mem i n → ∀ j, M.mem j n →
  ((∃ x, M.mem x A ∧ Rd_entry_d i x e ∧ Rd_entry_d j x e) ↔
    ∃ y, M.mem y B ∧ Rd_entry_d i y p ∧ Rd_entry_d j y p)

def At_prescribed_d (n A B e τ p : M.Domain) : Prop := ∀ i, M.mem i n →
  ∀ x, M.mem x A → ∀ y, M.mem y B → Rd_entry_d i x e → Rd_entry_d x y τ → Rd_entry_d i y p

def At_elementary_d (ω A R B S e n p : M.Domain) : Prop :=
  ∀ b l F E D q s t, M.mem b ω → Sfm_d I ω l F → Sbound_d I F b →
    M.IsFunctionSpace I E b A → M.IsFunctionSpace I D b B → Fn0_d b n q →
    Cp0_d b ω A q e s → Cp0_d b n B q p t → ∀ r, M.mem r l →
      (Ssat_d I A R E F l r s ↔ Ssat_d I B S D F l r t)

structure At_node_d (ω A R B S e τ n p : M.Domain) : Prop where
  length : M.mem n ω
  function : Fn0_d n B p
  coherent : At_coherent_d n A B e p
  prescribed : At_prescribed_d n A B e τ p
  elementary : At_elementary_d I ω A R B S e n p

variable (hZF : M.Models ZF)
local notation "I₀" => kp_pair_l (ZF.modelsKP hZF)

theorem At_node_d.prefix_l {ω A R B S e τ n m p s : M.Domain}
    (h : At_node_d I₀ ω A R B S e τ m p) (hn : M.mem n ω) (hs : Fn0_d n B s)
    (sub : M.MemberSubset s p) : At_node_d I₀ ω A R B S e τ n s := by
  have res := (Descriptive.ds_restrict_iff_l I₀ (fn0_function_l (ZF.modelsKP hZF) hs)
    (fn0_function_l (ZF.modelsKP hZF) h.function).1).mpr sub
  have hnm : M.MemberSubset n m := fun i hi => by
    obtain ⟨y, _, hiy⟩ := hs.2.1 i hi
    exact (h.function.bound_l ((res.2 i y).mp hiy).2).1
  have entry i y (hi : M.mem i n) : Rd_entry_d i y s ↔ Rd_entry_d i y p :=
    (res.2 i y).trans (and_iff_right hi)
  refine ⟨hn, hs, fun i hi j hj => ?_, fun i hi x hx y hy he hτ => ?_, ?_⟩
  · exact (h.coherent i (hnm i hi) j (hnm j hj)).trans (exists_congr fun y => and_congr_right fun _ =>
      and_congr (entry i y hi).symm (entry j y hj).symm)
  · exact (entry i y hi).mpr (h.prescribed i (hnm i hi) x hx y hy he hτ)
  · intro b l F E D q a t hb hF bound hE hD hq ha ht
    have ht' : Cp0_d b m B q p t := ⟨ht.1, fun i hi => by
      obtain ⟨k, hk, y, hy, hik, hky, hiy⟩ := ht.2 i hi
      exact ⟨k, hnm k hk, y, hy, hik, (entry k y hk).mp hky, hiy⟩⟩
    exact h.elementary b l F E D q a t hb hF bound hE hD (hq.mono_target_l hnm) ha ht'

theorem at_node_of_l {ω c d A R B S j e τ n p : M.Domain}
    (hω : M.IsOmega ω) (hm : Smdl_d I₀ c A R) (hn : Smdl_d I₀ d B S)
    (hj : Smap_d I₀ ω c d A B j) (he : Fn0_d ω A e)
    (hτj : ∀ x y, Rd_entry_d x y τ → Rd_entry_d x y j)
    (hnω : M.mem n ω) (hp : Cp0_d n A B e j p) : At_node_d I₀ ω A R B S e τ n p := by
  have maps i x y (hi : M.mem i n) (hex : Rd_entry_d i x e) (hpy : Rd_entry_d i y p) : Rd_entry_d x y j := by
    obtain ⟨a, ha, b, hb, hea, hab, hpb⟩ := hp.2 i hi
    have ex := (fn0_function_l (ZF.modelsKP hZF) he).1.2 i a x hea hex
    have ey := (fn0_function_l (ZF.modelsKP hZF) hp.1).1.2 i b y hpb hpy
    exact ex ▸ ey ▸ hab
  refine ⟨hnω, hp.1, fun i hi k hk => ⟨?_, ?_⟩, fun i hi x _ y _ hex hτ => ?_, ?_⟩
  · rintro ⟨x, _, hix, hkx⟩
    obtain ⟨y, hy, hiy⟩ := hp.1.2.1 i hi
    obtain ⟨z, _, hkz⟩ := hp.1.2.1 k hk
    exact ⟨y, hy, hiy, (hj.1.1.1.2 x z y (maps k x z hk hkx hkz) (maps i x y hi hix hiy)) ▸ hkz⟩
  · rintro ⟨y, _, hiy, hky⟩
    obtain ⟨x, hx, hix⟩ := he.2.1 i (hω.transitive hZF n hnω i hi)
    obtain ⟨z, _, hkz⟩ := he.2.1 k (hω.transitive hZF n hnω k hk)
    exact ⟨x, hx, hix, (hj.1.2 z x y (maps k z y hk hkz hky) (maps i x y hi hix hiy)) ▸ hkz⟩
  · obtain ⟨z, _, hiz⟩ := hp.1.2.1 i hi
    exact hj.1.1.1.2 x z y (maps i x z hi hex hiz) (hτj x y hτ) ▸ hiz
  · intro b l F E D q s t hb hF bound hE hD hq ha ht r hr
    have mapped : Cp0_d b A B s j t := ⟨ht.1, fun v hv => by
      obtain ⟨i, _, x, hx, hvi, hix, hvx⟩ := ha.2 v hv
      obtain ⟨k, hk, y, hy, hvk, hky, hvy⟩ := ht.2 v hv
      have eq := hq.2.2 v hv k hk i (hq.bound_l hvi).2 hvk hvi
      subst k
      exact ⟨x, hx, y, hy, hvx, maps i x y hk hix hky, hvy⟩⟩
    exact hj.finite_sat_l hZF hω hm hn hb hF bound hr hE hD ha.1 mapped

end YesMetaZFC.SetTheory.Internal
