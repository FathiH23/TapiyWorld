import * as d3 from 'd3';
import * as topojson from 'topojson-client';
import { escapeHtml } from '@/utils/sanitize';
import { getCSSColor } from '@/utils';
import type { Topology, GeometryCollection } from 'topojson-specification';
import type { Feature, Geometry } from 'geojson';
import type { 
  MapLayers, 
  Hotspot, 
  NewsItem, 
  InternetOutage, 
  RelatedAsset, 
  AssetType, 
  AisDisruptionEvent, 
  AisDensityZone, 
  CableAdvisory, 
  RepairShip, 
  SocialUnrestEvent, 
  MilitaryFlight, 
  MilitaryVessel, 
  MilitaryFlightCluster, 
  MilitaryVesselCluster, 
  NaturalEvent, 
  CyberThreat, 
  CableHealthRecord,
  MilitaryBase,
  ConflictZone,
  NuclearFacility,
  GammaIrradiator,
  Port,
  Spaceport,
  CriticalMineral
} from '@/types';
import type { AirportDelayAlert } from '@/services/aviation';
import type { Earthquake } from '@/services/earthquakes';
import type { IranEvent } from '@/services/conflict';
import type { TechHubActivity } from '@/services/tech-activity';
import type { GeoHubActivity } from '@/services/geo-activity';
import { getNaturalEventIcon } from '@/services/eonet';
import type { WeatherAlert } from '@/services/weather';
import { getSeverityColor } from '@/services/weather';
import {
  MAP_URLS,
  INTEL_HOTSPOTS,
  CONFLICT_ZONES,
  MILITARY_BASES,
  UNDERSEA_CABLES,
  NUCLEAR_FACILITIES,
  GAMMA_IRRADIATORS,
  PIPELINES,
  PIPELINE_COLORS,
  SANCTIONED_COUNTRIES,
  STRATEGIC_WATERWAYS,
  APT_GROUPS,
  ECONOMIC_CENTERS,
  AI_DATA_CENTERS,
  PORTS,
  SPACEPORTS,
  CRITICAL_MINERALS,
  SITE_VARIANT,
  STARTUP_HUBS,
  ACCELERATORS,
  TECH_HQS,
  CLOUD_REGIONS,
  STOCK_EXCHANGES,
  FINANCIAL_CENTERS,
  CENTRAL_BANKS,
  COMMODITY_HUBS,
} from '@/config';
import { tokenizeForMatch, matchKeyword, findMatchingKeywords } from '@/utils/keyword-match';
import { MapPopup } from './MapPopup';
import {
  updateHotspotEscalation,
  getHotspotEscalation,
  setMilitaryData,
  setCIIGetter,
  setGeoAlertGetter,
} from '@/services/hotspot-escalation';
import { getCountryScore } from '@/services/country-instability';
import { getAlertsNearLocation } from '@/services/geo-convergence';
import { getCountryAtCoordinates, getCountryBbox } from '@/services/country-geometry';
import type { CountryClickPayload } from './DeckGLMap';
import { t } from '@/services/i18n';

export type TimeRange = '1h' | '6h' | '24h' | '48h' | '7d' | 'all';
export type MapView = 'global' | 'america' | 'mena' | 'eu' | 'asia' | 'latam' | 'africa' | 'oceania';

interface MapState {
  zoom: number;
  pan: { x: number; y: number };
  view: MapView;
  layers: MapLayers;
  timeRange: TimeRange;
}

interface HotspotWithBreaking extends Hotspot {
  hasBreaking?: boolean;
}

interface TechEventMarker {
  id: string;
  title: string;
  location: string;
  lat: number;
  lng: number;
  country: string;
  startDate: string;
  endDate: string;
  url: string | null;
  daysUntil: number;
}

interface WorldTopology extends Topology {
  objects: {
    countries: GeometryCollection;
  };
}

export class MapComponent {
  private static readonly LAYER_ZOOM_THRESHOLDS: Partial<
    Record<keyof MapLayers, { minZoom: number; showLabels?: number }>
  > = {
    bases: { minZoom: 3, showLabels: 5 },
    nuclear: { minZoom: 2 },
    conflicts: { minZoom: 1, showLabels: 3 },
    economic: { minZoom: 2 },
    natural: { minZoom: 1, showLabels: 2 },
  };

  private container: HTMLElement;
  private svg: d3.Selection<SVGSVGElement, unknown, null, undefined>;
  private wrapper: HTMLElement;
  private overlays: HTMLElement;
  private canvas: HTMLCanvasElement;
  private ctx: CanvasRenderingContext2D | null = null;
  private state: MapState;
  private worldData: WorldTopology | null = null;
  private countryFeatures: Feature<Geometry>[] | null = null;
  private isResizing = false;
  private baseLayerGroup: d3.Selection<SVGGElement, unknown, null, undefined> | null = null;
  private dynamicLayerGroup: d3.Selection<SVGGElement, unknown, null, undefined> | null = null;
  private baseRendered = false;
  private baseWidth = 0;
  private baseHeight = 0;
  private hotspots: HotspotWithBreaking[];
  private earthquakes: Earthquake[] = [];
  private weatherAlerts: WeatherAlert[] = [];
  private outages: InternetOutage[] = [];
  private aisDisruptions: AisDisruptionEvent[] = [];
  private aisDensity: AisDensityZone[] = [];
  private cableAdvisories: CableAdvisory[] = [];
  private repairShips: RepairShip[] = [];
  private healthByCableId: Record<string, CableHealthRecord> = {};
  private protests: SocialUnrestEvent[] = [];
  private flightDelays: AirportDelayAlert[] = [];
  private militaryFlights: MilitaryFlight[] = [];
  private militaryFlightClusters: MilitaryFlightCluster[] = [];
  private militaryVessels: MilitaryVessel[] = [];
  private militaryVesselClusters: MilitaryVesselCluster[] = [];
  private naturalEvents: NaturalEvent[] = [];
  private firmsFireData: Array<{ lat: number; lon: number; brightness: number; frp: number; confidence: number; region: string; acq_date: string; daynight: string }> = [];
  private techEvents: TechEventMarker[] = [];
  private techActivities: TechHubActivity[] = [];
  private geoActivities: GeoHubActivity[] = [];
  private iranEvents: IranEvent[] = [];
  private news: NewsItem[] = [];
  private onTechHubClick?: (hub: TechHubActivity) => void;
  private onGeoHubClick?: (hub: GeoHubActivity) => void;
  private popup: MapPopup;
  private onHotspotClick?: (hotspot: Hotspot) => void;
  private onTimeRangeChange?: (range: TimeRange) => void;
  private onLayerChange?: (layer: keyof MapLayers, enabled: boolean, source: 'user' | 'programmatic') => void;
  private layerZoomOverrides: Partial<Record<keyof MapLayers, boolean>> = {};
  private onStateChange?: (state: MapState) => void;
  private onCountryClick?: (country: CountryClickPayload) => void;
  private highlightedAssets: Record<AssetType, Set<string>> = {
    pipeline: new Set(),
    cable: new Set(),
    datacenter: new Set(),
    base: new Set(),
    nuclear: new Set(),
  };
  private boundVisibilityHandler!: () => void;
  private renderScheduled = false;
  private lastRenderTime = 0;
  private readonly MIN_RENDER_INTERVAL_MS = 50; // Reduced from 100ms for better performance
  private healthCheckIntervalId: ReturnType<typeof setInterval> | null = null;
  private animationFrame: number | null = null;

  constructor(container: HTMLElement, initialState: MapState) {
    this.container = container;
    this.state = initialState;
    this.hotspots = [...INTEL_HOTSPOTS];

    this.wrapper = document.createElement('div');
    this.wrapper.className = 'map-wrapper';
    this.wrapper.id = 'mapWrapper';
    this.wrapper.style.cssText = `
      position: relative;
      width: 100%;
      height: 100%;
      overflow: hidden;
      background: #0f172a;
    `;

    const svgElement = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
    svgElement.classList.add('map-svg');
    svgElement.id = 'mapSvg';
    svgElement.style.cssText = `
      position: absolute;
      width: 100%;
      height: 100%;
      pointer-events: none;
    `;
    this.wrapper.appendChild(svgElement);

    this.canvas = document.createElement('canvas');
    this.canvas.className = 'map-canvas';
    this.canvas.id = 'mapCanvas';
    this.canvas.style.cssText = `
      position: absolute;
      width: 100%;
      height: 100%;
      pointer-events: none;
    `;
    this.wrapper.appendChild(this.canvas);
    this.ctx = this.canvas.getContext('2d');

    this.overlays = document.createElement('div');
    this.overlays.id = 'mapOverlays';
    this.overlays.style.cssText = `
      position: absolute;
      width: 100%;
      height: 100%;
      pointer-events: none;
    `;
    this.wrapper.appendChild(this.overlays);

    container.appendChild(this.wrapper);
    container.appendChild(this.createControls());
    container.appendChild(this.createTimeSlider());
    container.appendChild(this.createLayerToggles());
    container.appendChild(this.createLegend());

    this.svg = d3.select(svgElement);
    this.baseLayerGroup = this.svg.append('g').attr('class', 'map-base');
    this.dynamicLayerGroup = this.svg.append('g').attr('class', 'map-dynamic');
    this.popup = new MapPopup(container);

    this.setupZoomHandlers();
    this.loadMapData();
    this.setupResizeObserver();

    window.addEventListener('theme-changed', () => {
      this.baseRendered = false;
      this.scheduleRender();
    });
  }

  private setupResizeObserver(): void {
    let resizeTimeout: number;
    const resizeObserver = new ResizeObserver(() => {
      if (this.isResizing) return;
      clearTimeout(resizeTimeout);
      resizeTimeout = window.setTimeout(() => {
        this.scheduleRender();
      }, 100);
    });
    resizeObserver.observe(this.container);

    this.boundVisibilityHandler = () => {
      if (!document.hidden) {
        this.scheduleRender();
      }
    };
    document.addEventListener('visibilitychange', this.boundVisibilityHandler);
  }

  public setIsResizing(value: boolean): void {
    this.isResizing = value;
    if (!value) {
      this.scheduleRender();
    }
  }

  public destroy(): void {
    document.removeEventListener('visibilitychange', this.boundVisibilityHandler);
    if (this.healthCheckIntervalId) {
      clearInterval(this.healthCheckIntervalId);
    }
    if (this.animationFrame) {
      cancelAnimationFrame(this.animationFrame);
    }
  }

  private createControls(): HTMLElement {
    const controls = document.createElement('div');
    controls.className = 'map-controls';
    controls.style.cssText = `
      position: absolute;
      top: 16px;
      right: 16px;
      display: flex;
      gap: 8px;
      background: #1e293b;
      border-radius: 6px;
      padding: 4px;
      border: 1px solid #334155;
      z-index: 1000;
      pointer-events: auto;
    `;

    const buttons = [
      { action: 'zoom-in', icon: '+' },
      { action: 'zoom-out', icon: '−' },
      { action: 'reset', icon: '⟲' }
    ];

    buttons.forEach(({ action, icon }) => {
      const btn = document.createElement('button');
      btn.className = 'map-control-btn';
      btn.dataset.action = action;
      btn.textContent = icon;
      btn.style.cssText = `
        width: 32px;
        height: 32px;
        background: #2d3a4f;
        color: #e2e8f0;
        border: 1px solid #405570;
        border-radius: 4px;
        cursor: pointer;
        font-size: 18px;
        display: flex;
        align-items: center;
        justify-content: center;
        transition: background 0.15s;
      `;
      btn.addEventListener('mouseenter', () => { btn.style.background = '#3d4a63'; });
      btn.addEventListener('mouseleave', () => { btn.style.background = '#2d3a4f'; });
      controls.appendChild(btn);
    });

    controls.addEventListener('click', (e) => {
      const target = e.target as HTMLElement;
      const action = target.dataset.action;
      if (action === 'zoom-in') this.zoomIn();
      else if (action === 'zoom-out') this.zoomOut();
      else if (action === 'reset') this.reset();
    });

    return controls;
  }

  private createTimeSlider(): HTMLElement {
    const slider = document.createElement('div');
    slider.className = 'time-slider';
    slider.id = 'timeSlider';
    slider.style.cssText = `
      position: absolute;
      bottom: 16px;
      left: 50%;
      transform: translateX(-50%);
      background: #1e293b;
      border-radius: 6px;
      padding: 8px 12px;
      border: 1px solid #334155;
      display: flex;
      gap: 8px;
      align-items: center;
      z-index: 1000;
      pointer-events: auto;
    `;

    const ranges: { value: TimeRange; label: string }[] = [
      { value: '1h', label: '1H' },
      { value: '6h', label: '6H' },
      { value: '24h', label: '24H' },
      { value: '48h', label: '48H' },
      { value: '7d', label: '7D' },
      { value: 'all', label: 'ALL' },
    ];

    ranges.forEach(r => {
      const btn = document.createElement('button');
      btn.className = `time-btn ${this.state.timeRange === r.value ? 'active' : ''}`;
      btn.dataset.range = r.value;
      btn.textContent = r.label;
      btn.style.cssText = `
        padding: 4px 8px;
        background: ${this.state.timeRange === r.value ? '#2d5a8c' : '#2d3a4f'};
        color: #e2e8f0;
        border: 1px solid #405570;
        border-radius: 4px;
        font-size: 12px;
        cursor: pointer;
        transition: background 0.15s;
      `;
      btn.addEventListener('mouseenter', () => { 
        btn.style.background = this.state.timeRange === r.value ? '#3d6a9c' : '#3d4a63';
      });
      btn.addEventListener('mouseleave', () => { 
        btn.style.background = this.state.timeRange === r.value ? '#2d5a8c' : '#2d3a4f';
      });
      btn.addEventListener('click', () => this.setTimeRange(r.value));
      slider.appendChild(btn);
    });

    return slider;
  }

  private createLayerToggles(): HTMLElement {
    const toggles = document.createElement('div');
    toggles.className = 'layer-toggles';
    toggles.id = 'layerToggles';
    toggles.style.cssText = `
      position: absolute;
      top: 16px;
      left: 16px;
      background: #1e293b;
      border-radius: 6px;
      padding: 8px;
      border: 1px solid #334155;
      display: flex;
      flex-direction: column;
      gap: 4px;
      max-height: 400px;
      overflow-y: auto;
      z-index: 1000;
      pointer-events: auto;
    `;

    const layers = this.getLayersForVariant();
    
    layers.forEach(layer => {
      const btn = document.createElement('button');
      btn.className = `layer-toggle ${this.state.layers[layer] ? 'active' : ''}`;
      btn.dataset.layer = layer;
      btn.textContent = this.getLayerLabel(layer);
      btn.style.cssText = `
        padding: 6px 12px;
        background: ${this.state.layers[layer] ? '#2d5a8c' : '#2d3a4f'};
        color: #e2e8f0;
        border: 1px solid #405570;
        border-radius: 4px;
        font-size: 12px;
        cursor: pointer;
        text-align: left;
        white-space: nowrap;
        transition: background 0.15s;
      `;
      btn.addEventListener('mouseenter', () => { 
        btn.style.background = this.state.layers[layer] ? '#3d6a9c' : '#3d4a63';
      });
      btn.addEventListener('mouseleave', () => { 
        btn.style.background = this.state.layers[layer] ? '#2d5a8c' : '#2d3a4f';
      });
      btn.addEventListener('click', () => this.toggleLayer(layer));
      toggles.appendChild(btn);
    });

    return toggles;
  }

  private getLayersForVariant(): (keyof MapLayers)[] {
    if (SITE_VARIANT === 'tech') {
      return ['cables', 'datacenters', 'outages', 'startupHubs', 'cloudRegions', 'accelerators', 'techHQs', 'techEvents', 'natural', 'weather', 'economic'];
    } else if (SITE_VARIANT === 'finance') {
      return ['stockExchanges', 'financialCenters', 'centralBanks', 'commodityHubs', 'cables', 'pipelines', 'outages', 'sanctions', 'economic', 'waterways', 'natural', 'weather'];
    } else if (SITE_VARIANT === 'happy') {
      return ['positiveEvents', 'kindness', 'happiness', 'speciesRecovery', 'renewableInstallations'];
    } else {
      return [
        'iranAttacks', 'conflicts', 'hotspots', 'sanctions', 'protests',
        'bases', 'nuclear', 'irradiators', 'military',
        'cables', 'pipelines', 'outages', 'datacenters',
        'ais', 'flights', 'gpsJamming',
        'natural', 'weather', 'economic', 'waterways'
      ];
    }
  }

  private getLayerLabel(layer: keyof MapLayers): string {
    const labels: Partial<Record<keyof MapLayers, string>> = {
      hotspots: 'Intel Hotspots',
      conflicts: 'Conflicts',
      bases: 'Military Bases',
      nuclear: 'Nuclear Sites',
      irradiators: 'Gamma Irradiators',
      military: 'Military Activity',
      cables: 'Undersea Cables',
      pipelines: 'Pipelines',
      outages: 'Internet Outages',
      datacenters: 'AI Data Centers',
      ais: 'Ship Traffic',
      flights: 'Flight Delays',
      natural: 'Natural Events',
      weather: 'Weather Alerts',
      economic: 'Economic Centers',
      waterways: 'Waterways',
      startupHubs: 'Startup Hubs',
      cloudRegions: 'Cloud Regions',
      accelerators: 'Accelerators',
      techHQs: 'Tech HQs',
      techEvents: 'Tech Events',
      stockExchanges: 'Stock Exchanges',
      financialCenters: 'Financial Centers',
      centralBanks: 'Central Banks',
      commodityHubs: 'Commodity Hubs',
      iranAttacks: 'Iran Events',
      gpsJamming: 'GPS Jamming',
      sanctions: 'Sanctions',
      protests: 'Protests'
    };
    return labels[layer] || layer;
  }

  private createLegend(): HTMLElement {
    const legend = document.createElement('div');
    legend.className = 'map-legend';
    legend.style.cssText = `
      position: absolute;
      bottom: 16px;
      right: 16px;
      background: #1e293b;
      border-radius: 6px;
      padding: 8px 12px;
      border: 1px solid #334155;
      display: flex;
      flex-direction: column;
      gap: 4px;
      font-size: 11px;
      color: #94a3b8;
      z-index: 1000;
      pointer-events: none;
    `;

    if (SITE_VARIANT === 'tech') {
      legend.innerHTML = `
        <div style="display: flex; align-items: center; gap: 6px;"><span style="color: #8b5cf6;">●</span> Tech HQs</div>
        <div style="display: flex; align-items: center; gap: 6px;"><span style="color: #06b6d4;">●</span> Startup Hubs</div>
        <div style="display: flex; align-items: center; gap: 6px;"><span style="color: #f59e0b;">●</span> Cloud Regions</div>
        <div style="display: flex; align-items: center; gap: 6px;"><span style="color: #a855f7;">📅</span> Tech Events</div>
      `;
    } else {
      legend.innerHTML = `
        <div style="display: flex; align-items: center; gap: 6px;"><span style="color: #ef4444;">●</span> High Priority</div>
        <div style="display: flex; align-items: center; gap: 6px;"><span style="color: #f59e0b;">●</span> Elevated</div>
        <div style="display: flex; align-items: center; gap: 6px;"><span style="color: #94a3b8;">●</span> Monitoring</div>
        <div style="display: flex; align-items: center; gap: 6px;"><span style="color: #b91c1c;">⚔</span> Conflict</div>
        <div style="display: flex; align-items: center; gap: 6px;"><span style="color: #10b981;">●</span> Earthquake</div>
      `;
    }
    return legend;
  }

  private setupZoomHandlers(): void {
    let isDragging = false;
    let lastPos = { x: 0, y: 0 };
    let lastTouchDist = 0;
    let lastTouchCenter = { x: 0, y: 0 };

    const shouldIgnoreInteraction = (target: EventTarget | null): boolean => {
      if (!(target instanceof Element)) return false;
      return target.closest('.map-controls, .time-slider, .layer-toggles, .map-legend, .map-popup, button, select, input') !== null;
    };

    // Wheel zoom
    this.container.addEventListener('wheel', (e) => {
      e.preventDefault();
      if (shouldIgnoreInteraction(e.target)) return;

      if (e.ctrlKey) {
        this.state.zoom = Math.max(1, Math.min(10, this.state.zoom - e.deltaY * 0.01));
      } else {
        if (Math.abs(e.deltaX) > Math.abs(e.deltaY) * 0.5 || e.shiftKey) {
          const panSpeed = 2 / this.state.zoom;
          this.state.pan.x -= e.deltaX * panSpeed;
          this.state.pan.y -= e.deltaY * panSpeed;
        } else {
          const zoomDelta = e.deltaY > 0 ? -0.15 : 0.15;
          this.state.zoom = Math.max(1, Math.min(10, this.state.zoom + zoomDelta));
        }
      }
      this.applyTransform();
      this.scheduleRender();
    }, { passive: false });

    // Mouse drag
    this.container.addEventListener('mousedown', (e) => {
      if (shouldIgnoreInteraction(e.target)) return;
      if (e.button === 0) {
        isDragging = true;
        lastPos = { x: e.clientX, y: e.clientY };
        this.container.style.cursor = 'grabbing';
      }
    });

    document.addEventListener('mousemove', (e) => {
      if (!isDragging) return;

      const dx = e.clientX - lastPos.x;
      const dy = e.clientY - lastPos.y;
      const panSpeed = 1 / this.state.zoom;

      this.state.pan.x += dx * panSpeed;
      this.state.pan.y += dy * panSpeed;
      lastPos = { x: e.clientX, y: e.clientY };

      this.applyTransform();
      this.scheduleRender();
    });

    document.addEventListener('mouseup', () => {
      if (isDragging) {
        isDragging = false;
        this.container.style.cursor = 'grab';
      }
    });

    // Touch support
    this.container.addEventListener('touchstart', (e) => {
      if (shouldIgnoreInteraction(e.target)) return;
      e.preventDefault();

      if (e.touches.length === 2) {
        const touch1 = e.touches[0]!;
        const touch2 = e.touches[1]!;
        lastTouchDist = Math.hypot(
          touch2.clientX - touch1.clientX,
          touch2.clientY - touch1.clientY
        );
        lastTouchCenter = {
          x: (touch1.clientX + touch2.clientX) / 2,
          y: (touch1.clientY + touch2.clientY) / 2,
        };
      } else if (e.touches.length === 1) {
        isDragging = true;
        lastPos = { x: e.touches[0]!.clientX, y: e.touches[0]!.clientY };
      }
    }, { passive: false });

    this.container.addEventListener('touchmove', (e) => {
      e.preventDefault();

      if (e.touches.length === 2) {
        const touch1 = e.touches[0]!;
        const touch2 = e.touches[1]!;
        
        const dist = Math.hypot(
          touch2.clientX - touch1.clientX,
          touch2.clientY - touch1.clientY
        );
        
        const scale = dist / lastTouchDist;
        this.state.zoom = Math.max(1, Math.min(10, this.state.zoom * scale));
        lastTouchDist = dist;

        const center = {
          x: (touch1.clientX + touch2.clientX) / 2,
          y: (touch1.clientY + touch2.clientY) / 2,
        };
        
        const panSpeed = 1 / this.state.zoom;
        this.state.pan.x += (center.x - lastTouchCenter.x) * panSpeed;
        this.state.pan.y += (center.y - lastTouchCenter.y) * panSpeed;
        lastTouchCenter = center;

        this.applyTransform();
        this.scheduleRender();
      } else if (e.touches.length === 1 && isDragging) {
        const dx = e.touches[0]!.clientX - lastPos.x;
        const dy = e.touches[0]!.clientY - lastPos.y;
        const panSpeed = 1 / this.state.zoom;

        this.state.pan.x += dx * panSpeed;
        this.state.pan.y += dy * panSpeed;
        lastPos = { x: e.touches[0]!.clientX, y: e.touches[0]!.clientY };

        this.applyTransform();
        this.scheduleRender();
      }
    }, { passive: false });

    this.container.addEventListener('touchend', () => {
      isDragging = false;
      lastTouchDist = 0;
    });

    this.container.addEventListener('click', (e) => {
      if (!this.onCountryClick || shouldIgnoreInteraction(e.target)) return;

      const rect = this.container.getBoundingClientRect();
      const zoom = this.state.zoom;
      const width = this.container.clientWidth;
      const height = this.container.clientHeight;
      
      const centerOffsetX = (width / 2) * (1 - zoom);
      const centerOffsetY = (height / 2) * (1 - zoom);
      const tx = centerOffsetX + this.state.pan.x * zoom;
      const ty = centerOffsetY + this.state.pan.y * zoom;
      
      const rawX = (e.clientX - rect.left - tx) / zoom;
      const rawY = (e.clientY - rect.top - ty) / zoom;
      
      const projection = this.getProjection(width, height);
      if (!projection.invert) return;
      
      const coords = projection.invert([rawX, rawY]);
      if (!coords) return;
      
      const [lon, lat] = coords;
      const hit = getCountryAtCoordinates(lat, lon);
      if (hit) {
        this.onCountryClick({ lat, lon, code: hit.code, name: hit.name });
      }
    });

    this.container.style.cursor = 'grab';
  }

  private async loadMapData(): Promise<void> {
    try {
      const response = await fetch(MAP_URLS.world);
      this.worldData = await response.json();
      
      if (this.worldData) {
        const countries = topojson.feature(
          this.worldData,
          this.worldData.objects.countries
        );
        this.countryFeatures = 'features' in countries ? countries.features : [countries];
      }
      
      this.baseRendered = false;
      this.scheduleRender();
    } catch (e) {
      console.error('Failed to load map data:', e);
    }
  }

  private getProjection(width: number, height: number): d3.GeoProjection {
    const LAT_NORTH = 72;
    const LAT_SOUTH = -56;
    const LAT_RANGE = LAT_NORTH - LAT_SOUTH;
    const LAT_CENTER = (LAT_NORTH + LAT_SOUTH) / 2;

    const scaleForWidth = width / (2 * Math.PI);
    const scaleForHeight = height / (LAT_RANGE * Math.PI / 180);
    const scale = Math.min(scaleForWidth, scaleForHeight);

    return d3
      .geoEquirectangular()
      .scale(scale)
      .center([0, LAT_CENTER])
      .translate([width / 2, height / 2]);
  }

  public scheduleRender(): void {
    if (this.renderScheduled) return;
    this.renderScheduled = true;
    
    if (this.animationFrame) {
      cancelAnimationFrame(this.animationFrame);
    }
    
    this.animationFrame = requestAnimationFrame(() => {
      this.animationFrame = null;
      this.renderScheduled = false;
      this.render();
    });
  }

  public render(): void {
    const now = performance.now();
    if (now - this.lastRenderTime < this.MIN_RENDER_INTERVAL_MS) {
      this.scheduleRender();
      return;
    }
    this.lastRenderTime = now;

    const width = this.container.clientWidth;
    const height = this.container.clientHeight;

    if (width === 0 || height === 0) return;

    // Update canvas size
    if (this.canvas.width !== width || this.canvas.height !== height) {
      this.canvas.width = width;
      this.canvas.height = height;
    }

    // Update SVG viewBox
    this.svg.attr('viewBox', `0 0 ${width} ${height}`);

    // Ensure layer groups exist
    this.ensureLayerGroups();

    // Render base map if needed
    if (!this.baseRendered || width !== this.baseWidth || height !== this.baseHeight) {
      this.renderBaseLayer(width, height);
    }

    // Clear and render dynamic content
    this.clearDynamicLayer();
    this.renderDynamicLayers(width, height);
    this.renderOverlays(width, height);
    
    this.applyTransform();
  }

  private ensureLayerGroups(): void {
    const svgNode = this.svg.node();
    if (!svgNode) return;

    const existingBase = svgNode.querySelector('.map-base');
    const existingDynamic = svgNode.querySelector('.map-dynamic');

    if (!existingBase || this.baseLayerGroup?.node() !== existingBase) {
      svgNode.querySelectorAll('.map-base, .map-dynamic').forEach(el => el.remove());
      this.baseLayerGroup = this.svg.append('g').attr('class', 'map-base');
      this.dynamicLayerGroup = this.svg.append('g').attr('class', 'map-dynamic');
      this.baseRendered = false;
    }
  }

  private renderBaseLayer(width: number, height: number): void {
    if (!this.baseLayerGroup || !this.countryFeatures) return;

    this.baseWidth = width;
    this.baseHeight = height;
    
    const baseNode = this.baseLayerGroup.node()!;
    while (baseNode.firstChild) baseNode.removeChild(baseNode.firstChild);

    const projection = this.getProjection(width, height);
    const path = d3.geoPath().projection(projection);

    // Background
    this.baseLayerGroup
      .append('rect')
      .attr('x', -width)
      .attr('y', -height)
      .attr('width', width * 3)
      .attr('height', height * 3)
      .attr('fill', '#0f172a');

    // Graticule
    const graticule = d3.geoGraticule();
    this.baseLayerGroup
      .append('path')
      .datum(graticule())
      .attr('d', path)
      .attr('fill', 'none')
      .attr('stroke', '#1e293b')
      .attr('stroke-width', 0.4);

    // Countries
    this.baseLayerGroup
      .selectAll('.country')
      .data(this.countryFeatures)
      .enter()
      .append('path')
      .attr('class', 'country')
      .attr('d', path as any)
      .attr('fill', '#1e293b')
      .attr('stroke', '#334155')
      .attr('stroke-width', 0.7);

    this.baseRendered = true;
    this.updateCountryFills();
  }

  private clearDynamicLayer(): void {
    if (this.ctx) {
      this.ctx.clearRect(0, 0, this.canvas.width, this.canvas.height);
    }
    
    const dynamicNode = this.dynamicLayerGroup?.node();
    if (dynamicNode) {
      while (dynamicNode.firstChild) dynamicNode.removeChild(dynamicNode.firstChild);
    }
    this.dynamicLayerGroup?.append('g').attr('class', 'overlays-svg');
  }

  private renderDynamicLayers(width: number, height: number): void {
    const projection = this.getProjection(width, height);

    // SVG-based layers (lines, polygons)
    if (this.state.layers.cables) {
      this.renderCables(projection);
    }

    if (this.state.layers.pipelines) {
      this.renderPipelines(projection);
    }

    if (this.state.layers.conflicts) {
      this.renderConflicts(projection);
    }

    if (this.state.layers.ais) {
      this.renderAisDensity(projection);
    }

    // Canvas-based layers (markers, tracks)
    if (this.ctx) {
      this.renderCanvasLayers(projection);
    }
  }

  private renderCanvasLayers(projection: d3.GeoProjection): void {
    if (!this.ctx) return;

    // Military tracks
    if (this.state.layers.military && this.state.zoom >= 2) {
      this.renderMilitaryTracks(projection);
    }

    // Military flights
    if (this.state.layers.military && this.state.layers.flights) {
      this.renderMilitaryFlights(projection);
    }

    // Military vessels
    if (this.state.layers.military && this.state.layers.vessels) {
      this.renderMilitaryVessels(projection);
    }
  }

  private renderMilitaryTracks(projection: d3.GeoProjection): void {
    if (!this.ctx) return;

    this.ctx.save();
    this.ctx.strokeStyle = '#4a5568';
    this.ctx.lineWidth = 1;
    this.ctx.setLineDash([3, 3]);

    // Flight tracks
    this.militaryFlights.forEach(flight => {
      if (!flight.track || flight.track.length < 2) return;
      
      this.ctx.beginPath();
      let first = true;
      
      flight.track.forEach(point => {
        const pos = projection([point[1], point[0]]);
        if (!pos) return;
        
        if (first) {
          this.ctx.moveTo(pos[0], pos[1]);
          first = false;
        } else {
          this.ctx.lineTo(pos[0], pos[1]);
        }
      });
      
      this.ctx.strokeStyle = flight.operator === 'us' ? '#60a5fa' : 
                            flight.operator === 'ru' ? '#f87171' : '#94a3b8';
      this.ctx.stroke();
    });

    // Vessel tracks
    this.militaryVessels.forEach(vessel => {
      if (!vessel.track || vessel.track.length < 2) return;
      
      this.ctx.beginPath();
      let first = true;
      
      vessel.track.forEach(point => {
        const pos = projection([point[1], point[0]]);
        if (!pos) return;
        
        if (first) {
          this.ctx.moveTo(pos[0], pos[1]);
          first = false;
        } else {
          this.ctx.lineTo(pos[0], pos[1]);
        }
      });
      
      this.ctx.strokeStyle = vessel.operator === 'us' ? '#60a5fa' : 
                            vessel.operator === 'ru' ? '#f87171' : '#94a3b8';
      this.ctx.stroke();
    });

    this.ctx.restore();
  }

  private renderMilitaryFlights(projection: d3.GeoProjection): void {
    if (!this.ctx) return;

    const clusters = this.clusterMarkers(this.militaryFlights, projection, 20);
    
    clusters.forEach(cluster => {
      if (cluster.count > 1) {
        // Draw cluster
        this.ctx.beginPath();
        this.ctx.arc(cluster.pos[0], cluster.pos[1], 12, 0, 2 * Math.PI);
        this.ctx.fillStyle = '#475569';
        this.ctx.fill();
        this.ctx.strokeStyle = '#94a3b8';
        this.ctx.lineWidth = 1;
        this.ctx.stroke();

        this.ctx.fillStyle = '#f8fafc';
        this.ctx.font = 'bold 10px monospace';
        this.ctx.textAlign = 'center';
        this.ctx.textBaseline = 'middle';
        this.ctx.fillText(cluster.count.toString(), cluster.pos[0], cluster.pos[1]);
      } else {
        const flight = cluster.items[0]!;
        const angle = flight.heading * Math.PI / 180;
        
        this.ctx.save();
        this.ctx.translate(cluster.pos[0], cluster.pos[1]);
        this.ctx.rotate(angle);
        
        // Aircraft symbol (no glow)
        this.ctx.beginPath();
        this.ctx.moveTo(8, 0);
        this.ctx.lineTo(-4, -4);
        this.ctx.lineTo(-4, 4);
        this.ctx.closePath();
        
        this.ctx.fillStyle = flight.isInteresting ? '#f97316' : 
                            flight.operator === 'us' ? '#3b82f6' : 
                            flight.operator === 'ru' ? '#ef4444' : '#6b7280';
        this.ctx.fill();
        this.ctx.strokeStyle = '#f8fafc';
        this.ctx.lineWidth = 1;
        this.ctx.stroke();
        
        this.ctx.restore();

        // Label at higher zoom
        if (this.state.zoom >= 3 && this.state.layers.labels) {
          this.ctx.fillStyle = '#cbd5e1';
          this.ctx.font = '9px monospace';
          this.ctx.fillText(
            flight.callsign || '?',
            cluster.pos[0] + 12,
            cluster.pos[1] - 8
          );
        }
      }
    });
  }

  private renderMilitaryVessels(projection: d3.GeoProjection): void {
    if (!this.ctx) return;

    const clusters = this.clusterMarkers(this.militaryVessels, projection, 20);
    
    clusters.forEach(cluster => {
      if (cluster.count > 1) {
        // Draw cluster
        this.ctx.beginPath();
        this.ctx.arc(cluster.pos[0], cluster.pos[1], 12, 0, 2 * Math.PI);
        this.ctx.fillStyle = '#475569';
        this.ctx.fill();
        this.ctx.strokeStyle = '#94a3b8';
        this.ctx.lineWidth = 1;
        this.ctx.stroke();

        this.ctx.fillStyle = '#f8fafc';
        this.ctx.font = 'bold 10px monospace';
        this.ctx.textAlign = 'center';
        this.ctx.textBaseline = 'middle';
        this.ctx.fillText(cluster.count.toString(), cluster.pos[0], cluster.pos[1]);
      } else {
        const vessel = cluster.items[0]!;
        const angle = vessel.heading * Math.PI / 180;
        
        this.ctx.save();
        this.ctx.translate(cluster.pos[0], cluster.pos[1]);
        this.ctx.rotate(angle);
        
        // Vessel symbol (diamond)
        this.ctx.beginPath();
        this.ctx.moveTo(0, -6);
        this.ctx.lineTo(4, 0);
        this.ctx.lineTo(0, 6);
        this.ctx.lineTo(-4, 0);
        this.ctx.closePath();
        
        this.ctx.fillStyle = vessel.isDark ? '#7f1d1d' : 
                            vessel.operator === 'us' ? '#3b82f6' : 
                            vessel.operator === 'ru' ? '#ef4444' : '#6b7280';
        this.ctx.fill();
        this.ctx.strokeStyle = '#f8fafc';
        this.ctx.lineWidth = 1;
        this.ctx.stroke();

        // Dark vessel indicator
        if (vessel.isDark) {
          this.ctx.fillStyle = '#ef4444';
          this.ctx.font = 'bold 10px monospace';
          this.ctx.fillText('!', 8, -8);
        }
        
        this.ctx.restore();

        // Label at higher zoom
        if (this.state.zoom >= 3 && this.state.layers.labels) {
          this.ctx.fillStyle = '#cbd5e1';
          this.ctx.font = '9px monospace';
          this.ctx.fillText(
            vessel.name || '?',
            cluster.pos[0] + 12,
            cluster.pos[1] - 8
          );
        }
      }
    });
  }

  private clusterMarkers<T extends { lat: number; lon: number }>(
    items: T[],
    projection: d3.GeoProjection,
    radius = 20
  ): Array<{ items: T[]; count: number; pos: [number, number] }> {
    if (items.length === 0) return [];
    
    // If zoomed in enough, return individual items
    if (this.state.zoom >= 3) {
      return items
        .filter(item => Number.isFinite(item.lat) && Number.isFinite(item.lon))
        .map(item => {
          const pos = projection([item.lon, item.lat]);
          return pos ? { items: [item], count: 1, pos } : null;
        })
        .filter((c): c is NonNullable<typeof c> => c !== null);
    }

    // Simple grid-based clustering for performance
    const clusters: Array<{ items: T[]; pos: [number, number] }> = [];
    const cellSize = radius * 2;
    const grid = new Map<string, T[]>();

    items.forEach(item => {
      if (!Number.isFinite(item.lat) || !Number.isFinite(item.lon)) return;
      
      const pos = projection([item.lon, item.lat]);
      if (!pos) return;

      const cellX = Math.floor(pos[0] / cellSize);
      const cellY = Math.floor(pos[1] / cellSize);
      const key = `${cellX},${cellY}`;
      
      if (!grid.has(key)) grid.set(key, []);
      grid.get(key)!.push(item);
    });

    grid.forEach((cellItems, key) => {
      if (cellItems.length === 0) return;

      // Calculate center
      const [cellX, cellY] = key.split(',').map(Number);
      const pos: [number, number] = [
        cellX * cellSize + cellSize / 2,
        cellY * cellSize + cellSize / 2
      ];

      clusters.push({
        items: cellItems,
        pos
      });
    });

    return clusters.map(c => ({
      ...c,
      count: c.items.length
    }));
  }

  private renderCables(projection: d3.GeoProjection): void {
    if (!this.dynamicLayerGroup) return;
    
    const group = this.dynamicLayerGroup.append('g').attr('class', 'cables');
    const lineGenerator = d3
      .line<[number, number]>()
      .x(d => projection(d)?.[0] ?? 0)
      .y(d => projection(d)?.[1] ?? 0)
      .curve(d3.curveCardinal);

    UNDERSEA_CABLES.forEach(cable => {
      const path = group
        .append('path')
        .attr('d', lineGenerator(cable.points))
        .attr('fill', 'none')
        .attr('stroke', '#60a5fa')
        .attr('stroke-width', 1.5)
        .attr('stroke-opacity', 0.6)
        .attr('data-cable-id', cable.id);

      path.append('title').text(cable.name);

      path.on('click', (event: MouseEvent) => {
        event.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        this.popup.show({
          type: 'cable',
          data: cable,
          x: event.clientX - rect.left,
          y: event.clientY - rect.top,
        });
      });
    });
  }

  private renderPipelines(projection: d3.GeoProjection): void {
    if (!this.dynamicLayerGroup) return;
    
    const group = this.dynamicLayerGroup.append('g').attr('class', 'pipelines');
    const lineGenerator = d3
      .line<[number, number]>()
      .x(d => projection(d)?.[0] ?? 0)
      .y(d => projection(d)?.[1] ?? 0)
      .curve(d3.curveCardinal);

    PIPELINES.forEach(pipeline => {
      const color = PIPELINE_COLORS[pipeline.type] || '#94a3b8';
      
      group
        .append('path')
        .attr('d', lineGenerator(pipeline.points))
        .attr('fill', 'none')
        .attr('stroke', color)
        .attr('stroke-width', 2)
        .attr('stroke-opacity', 0.8)
        .attr('stroke-dasharray', pipeline.status === 'construction' ? '4,2' : 'none')
        .attr('data-pipeline-id', pipeline.id)
        .append('title')
        .text(`${pipeline.name} (${pipeline.type})`);
    });
  }

  private renderConflicts(projection: d3.GeoProjection): void {
    if (!this.dynamicLayerGroup) return;
    
    const group = this.dynamicLayerGroup.append('g').attr('class', 'conflicts');

    CONFLICT_ZONES.forEach(zone => {
      const points = zone.coords
        .map(c => projection(c as [number, number]))
        .filter((p): p is [number, number] => p !== null);

      if (points.length > 0) {
        group
          .append('polygon')
          .attr('points', points.map(p => p.join(',')).join(' '))
          .attr('fill', 'rgba(180, 40, 40, 0.15)')
          .attr('stroke', '#b91c1c')
          .attr('stroke-width', 1.5)
          .attr('stroke-dasharray', '4,2');
      }
    });
  }

  private renderAisDensity(projection: d3.GeoProjection): void {
    if (!this.dynamicLayerGroup) return;
    
    const group = this.dynamicLayerGroup.append('g').attr('class', 'ais-density');

    this.aisDensity.forEach(zone => {
      const pos = projection([zone.lon, zone.lat]);
      if (!pos) return;

      const intensity = Math.min(Math.max(zone.intensity, 0.15), 1);
      const radius = 4 + intensity * 8;

      group
        .append('circle')
        .attr('cx', pos[0])
        .attr('cy', pos[1])
        .attr('r', radius)
        .attr('fill', zone.deltaPct >= 15 ? '#f59e0b' : '#60a5fa')
        .attr('fill-opacity', 0.2 + intensity * 0.2)
        .attr('stroke', 'none');
    });
  }

  private renderOverlays(width: number, height: number): void {
    this.overlays.innerHTML = '';
    
    const projection = this.getProjection(width, height);

    // Waterways
    if (this.state.layers.waterways) {
      this.renderWaterways(projection);
    }

    // Ports
    if (this.state.layers.ais) {
      this.renderPorts(projection);
    }

    // APT groups
    if (SITE_VARIANT !== 'tech') {
      this.renderAPTMarkers(projection);
    }

    // Nuclear facilities
    if (this.state.layers.nuclear) {
      this.renderNuclearFacilities(projection);
    }

    // Gamma irradiators
    if (this.state.layers.irradiators) {
      this.renderGammaIrradiators(projection);
    }

    // Hotspots
    if (this.state.layers.hotspots) {
      this.renderHotspots(projection);
    }

    // Military bases (additional HTML overlays)
    if (this.state.layers.bases) {
      this.renderMilitaryBases(projection);
    }

    // Earthquakes
    if (this.state.layers.natural) {
      this.renderEarthquakes(projection);
    }

    // Economic centers
    if (this.state.layers.economic) {
      this.renderEconomicCenters(projection);
    }

    // Weather alerts
    if (this.state.layers.weather) {
      this.renderWeatherAlerts(projection);
    }

    // Internet outages
    if (this.state.layers.outages) {
      this.renderOutages(projection);
    }

    // Cable advisories
    if (this.state.layers.cables) {
      this.renderCableAdvisories(projection);
    }

    // AI Data Centers
    if (this.state.layers.datacenters) {
      this.renderDataCenters(projection);
    }

    // Spaceports
    if (this.state.layers.spaceports) {
      this.renderSpaceports(projection);
    }

    // Critical minerals
    if (this.state.layers.minerals) {
      this.renderCriticalMinerals(projection);
    }

    // Tech variant layers
    if (SITE_VARIANT === 'tech') {
      if (this.state.layers.startupHubs) this.renderStartupHubs(projection);
      if (this.state.layers.cloudRegions) this.renderCloudRegions(projection);
      if (this.state.layers.techHQs) this.renderTechHQs(projection);
      if (this.state.layers.accelerators) this.renderAccelerators(projection);
      if (this.state.layers.techEvents) this.renderTechEvents(projection);
    }

    // Finance variant layers
    if (SITE_VARIANT === 'finance') {
      if (this.state.layers.stockExchanges) this.renderStockExchanges(projection);
      if (this.state.layers.financialCenters) this.renderFinancialCenters(projection);
      if (this.state.layers.centralBanks) this.renderCentralBanks(projection);
      if (this.state.layers.commodityHubs) this.renderCommodityHubs(projection);
    }

    // Iran events
    if (this.state.layers.iranAttacks && this.iranEvents.length > 0) {
      this.renderIranEvents(projection);
    }

    // Protests
    if (this.state.layers.protests) {
      this.renderProtests(projection);
    }

    // Flight delays
    if (this.state.layers.flights) {
      this.renderFlightDelays(projection);
    }

    // Natural events
    if (this.state.layers.natural) {
      this.renderNaturalEvents(projection);
    }

    // Fires
    if (this.state.layers.fires) {
      this.renderFires(projection);
    }
  }

  private renderWaterways(projection: d3.GeoProjection): void {
    STRATEGIC_WATERWAYS.forEach(waterway => {
      const pos = projection([waterway.lon, waterway.lat]);
      if (!pos) return;

      const el = document.createElement('div');
      el.className = 'waterway-marker';
      el.style.cssText = `
        position: absolute;
        left: ${pos[0]}px;
        top: ${pos[1]}px;
        width: 8px;
        height: 8px;
        background: #60a5fa;
        border: 1px solid #93c5fd;
        transform: translate(-50%, -50%) rotate(45deg);
        cursor: pointer;
        pointer-events: auto;
      `;
      el.title = waterway.name;

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        this.popup.show({
          type: 'waterway',
          data: waterway,
          x: e.clientX - rect.left,
          y: e.clientY - rect.top,
        });
      });

      this.overlays.appendChild(el);
    });
  }

  private renderPorts(projection: d3.GeoProjection): void {
    PORTS.forEach(port => {
      const pos = projection([port.lon, port.lat]);
      if (!pos) return;

      const el = document.createElement('div');
      el.className = 'port-marker';
      el.style.cssText = `
        position: absolute;
        left: ${pos[0]}px;
        top: ${pos[1]}px;
        transform: translate(-50%, -50%);
        color: ${port.type === 'naval' ? '#ef4444' : '#f59e0b'};
        font-size: 16px;
        cursor: pointer;
        pointer-events: auto;
        text-shadow: 0 1px 2px rgba(0,0,0,0.5);
      `;
      el.textContent = port.type === 'naval' ? '⚓' : '⚓';
      el.title = port.name;

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        this.popup.show({
          type: 'port',
          data: port,
          x: e.clientX - rect.left,
          y: e.clientY - rect.top,
        });
      });

      this.overlays.appendChild(el);
    });
  }

  private renderAPTMarkers(projection: d3.GeoProjection): void {
    APT_GROUPS.forEach(apt => {
      const pos = projection([apt.lon, apt.lat]);
      if (!pos) return;

      const el = document.createElement('div');
      el.className = 'apt-marker';
      el.style.cssText = `
        position: absolute;
        left: ${pos[0]}px;
        top: ${pos[1]}px;
        transform: translate(-50%, -50%);
        color: #f59e0b;
        font-size: 14px;
        cursor: pointer;
        pointer-events: auto;
      `;
      el.textContent = '⚠';
      el.title = apt.name;

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        this.popup.show({
          type: 'apt',
          data: apt,
          x: e.clientX - rect.left,
          y: e.clientY - rect.top,
        });
      });

      this.overlays.appendChild(el);
    });
  }

  private renderNuclearFacilities(projection: d3.GeoProjection): void {
    NUCLEAR_FACILITIES.forEach(facility => {
      const pos = projection([facility.lon, facility.lat]);
      if (!pos) return;

      const el = document.createElement('div');
      el.className = 'nuclear-marker';
      el.style.cssText = `
        position: absolute;
        left: ${pos[0]}px;
        top: ${pos[1]}px;
        width: 10px;
        height: 10px;
        background: ${facility.status === 'operational' ? '#f59e0b' : '#94a3b8'};
        border: 1px solid #f8fafc;
        border-radius: 50%;
        transform: translate(-50%, -50%);
        cursor: pointer;
        pointer-events: auto;
      `;
      el.title = `${facility.name} (${facility.status})`;

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        this.popup.show({
          type: 'nuclear',
          data: facility,
          x: e.clientX - rect.left,
          y: e.clientY - rect.top,
        });
      });

      this.overlays.appendChild(el);
    });
  }

  private renderGammaIrradiators(projection: d3.GeoProjection): void {
    GAMMA_IRRADIATORS.forEach(irradiator => {
      const pos = projection([irradiator.lon, irradiator.lat]);
      if (!pos) return;

      const el = document.createElement('div');
      el.className = 'irradiator-marker';
      el.style.cssText = `
        position: absolute;
        left: ${pos[0]}px;
        top: ${pos[1]}px;
        width: 8px;
        height: 8px;
        background: #f97316;
        border: 1px solid #fdba74;
        border-radius: 2px;
        transform: translate(-50%, -50%) rotate(45deg);
        cursor: pointer;
        pointer-events: auto;
      `;
      el.title = `${irradiator.city}, ${irradiator.country}`;

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        this.popup.show({
          type: 'irradiator',
          data: irradiator,
          x: e.clientX - rect.left,
          y: e.clientY - rect.top,
        });
      });

      this.overlays.appendChild(el);
    });
  }

  private renderHotspots(projection: d3.GeoProjection): void {
    this.hotspots.forEach(spot => {
      const pos = projection([spot.lon, spot.lat]);
      if (!pos) return;

      const el = document.createElement('div');
      el.className = 'hotspot';
      el.style.cssText = `
        position: absolute;
        left: ${pos[0]}px;
        top: ${pos[1]}px;
        transform: translate(-50%, -50%);
        cursor: pointer;
        pointer-events: auto;
      `;

      const color = spot.level === 'high' ? '#ef4444' : 
                    spot.level === 'elevated' ? '#f59e0b' : '#94a3b8';

      const marker = document.createElement('div');
      marker.style.cssText = `
        width: 12px;
        height: 12px;
        background: ${color};
        border: 2px solid #f8fafc;
        border-radius: 50%;
      `;
      el.appendChild(marker);

      if (spot.hasBreaking) {
        const badge = document.createElement('div');
        badge.style.cssText = `
          position: absolute;
          top: -8px;
          right: -8px;
          background: #b91c1c;
          color: white;
          font-size: 8px;
          padding: 2px 4px;
          border-radius: 2px;
          font-weight: bold;
        `;
        badge.textContent = 'BREAKING';
        el.appendChild(badge);
      }

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const relatedNews = this.getRelatedNews(spot);
        const rect = this.container.getBoundingClientRect();
        this.popup.show({
          type: 'hotspot',
          data: spot,
          relatedNews,
          x: e.clientX - rect.left,
          y: e.clientY - rect.top,
        });
        this.popup.loadHotspotGdeltContext(spot);
        this.onHotspotClick?.(spot);
      });

      this.overlays.appendChild(el);
    });
  }

  private renderMilitaryBases(projection: d3.GeoProjection): void {
    MILITARY_BASES.forEach(base => {
      const pos = projection([base.lon, base.lat]);
      if (!pos) return;

      const el = document.createElement('div');
      el.className = 'base-marker';
      el.style.cssText = `
        position: absolute;
        left: ${pos[0]}px;
        top: ${pos[1]}px;
        transform: translate(-50%, -50%);
        cursor: pointer;
        pointer-events: auto;
      `;

      const marker = document.createElement('div');
      marker.style.cssText = `
        width: 10px;
        height: 10px;
        background: ${base.country === 'US' ? '#3b82f6' : 
                     base.country === 'RU' ? '#ef4444' : 
                     base.country === 'CN' ? '#f59e0b' : '#6b7280'};
        border: 2px solid #f8fafc;
        transform: rotate(45deg);
      `;
      el.appendChild(marker);

      if (this.state.zoom >= 3 && this.state.layers.labels) {
        const label = document.createElement('div');
        label.style.cssText = `
          position: absolute;
          left: 14px;
          top: -4px;
          color: #cbd5e1;
          font-size: 9px;
          white-space: nowrap;
          text-shadow: 0 1px 2px rgba(0,0,0,0.5);
        `;
        label.textContent = base.name;
        el.appendChild(label);
      }

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        this.popup.show({
          type: 'base',
          data: base,
          x: e.clientX - rect.left,
          y: e.clientY - rect.top,
        });
      });

      this.overlays.appendChild(el);
    });
  }

  private renderEarthquakes(projection: d3.GeoProjection): void {
    const filteredQuakes = this.state.timeRange === 'all'
      ? this.earthquakes
      : this.earthquakes.filter(eq => eq.occurredAt >= Date.now() - this.getTimeRangeMs());

    filteredQuakes.forEach(eq => {
      const pos = projection([eq.location?.longitude ?? 0, eq.location?.latitude ?? 0]);
      if (!pos) return;

      const size = Math.max(6, eq.magnitude * 2.5);
      
      const el = document.createElement('div');
      el.className = 'earthquake-marker';
      el.style.cssText = `
        position: absolute;
        left: ${pos[0]}px;
        top: ${pos[1]}px;
        width: ${size}px;
        height: ${size}px;
        background: #ef4444;
        border: 1px solid #f8fafc;
        border-radius: 50% 50% 0 50%;
        transform: translate(-50%, -50%) rotate(45deg);
        cursor: pointer;
        pointer-events: auto;
      `;
      el.title = `M${eq.magnitude.toFixed(1)} - ${eq.place}`;

      if (this.state.zoom >= 2) {
        const label = document.createElement('div');
        label.style.cssText = `
          position: absolute;
          left: ${size}px;
          top: -${size/2}px;
          color: #f8fafc;
          font-size: 9px;
          white-space: nowrap;
          background: rgba(0,0,0,0.5);
          padding: 2px 4px;
          border-radius: 2px;
        `;
        label.textContent = `M${eq.magnitude.toFixed(1)}`;
        el.appendChild(label);
      }

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        this.popup.show({
          type: 'earthquake',
          data: eq,
          x: e.clientX - rect.left,
          y: e.clientY - rect.top,
        });
      });

      this.overlays.appendChild(el);
    });
  }

  private renderEconomicCenters(projection: d3.GeoProjection): void {
    ECONOMIC_CENTERS.forEach(center => {
      const pos = projection([center.lon, center.lat]);
      if (!pos) return;

      const el = document.createElement('div');
      el.className = 'economic-marker';
      el.style.cssText = `
        position: absolute;
        left: ${pos[0]}px;
        top: ${pos[1]}px;
        transform: translate(-50%, -50%);
        color: #60a5fa;
        font-size: 16px;
        cursor: pointer;
        pointer-events: auto;
        text-shadow: 0 1px 2px rgba(0,0,0,0.5);
      `;
      el.textContent = center.type === 'exchange' ? '📈' : 
                       center.type === 'central-bank' ? '🏛' : '💰';
      el.title = center.name;

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        this.popup.show({
          type: 'economic',
          data: center,
          x: e.clientX - rect.left,
          y: e.clientY - rect.top,
        });
      });

      this.overlays.appendChild(el);
    });
  }

  private renderWeatherAlerts(projection: d3.GeoProjection): void {
    this.weatherAlerts.forEach(alert => {
      if (!alert.centroid) return;
      
      const pos = projection(alert.centroid);
      if (!pos) return;

      const color = getSeverityColor(alert.severity);
      
      const el = document.createElement('div');
      el.className = 'weather-marker';
      el.style.cssText = `
        position: absolute;
        left: ${pos[0]}px;
        top: ${pos[1]}px;
        transform: translate(-50%, -50%);
        color: ${color};
        font-size: 16px;
        cursor: pointer;
        pointer-events: auto;
        text-shadow: 0 1px 2px rgba(0,0,0,0.5);
      `;
      el.textContent = '⚠';
      el.title = alert.headline || alert.event;

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        this.popup.show({
          type: 'weather',
          data: alert,
          x: e.clientX - rect.left,
          y: e.clientY - rect.top,
        });
      });

      this.overlays.appendChild(el);
    });
  }

  private renderOutages(projection: d3.GeoProjection): void {
    this.outages.forEach(outage => {
      const pos = projection([outage.lon, outage.lat]);
      if (!pos) return;

      const color = outage.severity === 'high' ? '#ef4444' :
                    outage.severity === 'medium' ? '#f59e0b' : '#94a3b8';

      const el = document.createElement('div');
      el.className = 'outage-marker';
      el.style.cssText = `
        position: absolute;
        left: ${pos[0]}px;
        top: ${pos[1]}px;
        transform: translate(-50%, -50%);
        color: ${color};
        font-size: 16px;
        cursor: pointer;
        pointer-events: auto;
        text-shadow: 0 1px 2px rgba(0,0,0,0.5);
      `;
      el.textContent = '📡';
      el.title = `${outage.country}: ${outage.reason || 'Internet outage'}`;

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        this.popup.show({
          type: 'outage',
          data: outage,
          x: e.clientX - rect.left,
          y: e.clientY - rect.top,
        });
      });

      this.overlays.appendChild(el);
    });
  }

  private renderCableAdvisories(projection: d3.GeoProjection): void {
    this.cableAdvisories.forEach(advisory => {
      const pos = projection([advisory.lon, advisory.lat]);
      if (!pos) return;

      const color = advisory.severity === 'fault' ? '#ef4444' : '#f59e0b';

      const el = document.createElement('div');
      el.className = 'cable-advisory-marker';
      el.style.cssText = `
        position: absolute;
        left: ${pos[0]}px;
        top: ${pos[1]}px;
        transform: translate(-50%, -50%);
        color: ${color};
        font-size: 16px;
        cursor: pointer;
        pointer-events: auto;
        text-shadow: 0 1px 2px rgba(0,0,0,0.5);
      `;
      el.textContent = advisory.severity === 'fault' ? '⚡' : '⚠';
      el.title = `${this.getCableName(advisory.cableId)}: ${advisory.description || 'Cable issue'}`;

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        this.popup.show({
          type: 'cable-advisory',
          data: advisory,
          x: e.clientX - rect.left,
          y: e.clientY - rect.top,
        });
      });

      this.overlays.appendChild(el);
    });

    this.repairShips.forEach(ship => {
      const pos = projection([ship.lon, ship.lat]);
      if (!pos) return;

      const el = document.createElement('div');
      el.className = 'repair-ship-marker';
      el.style.cssText = `
        position: absolute;
        left: ${pos[0]}px;
        top: ${pos[1]}px;
        transform: translate(-50%, -50%);
        color: #60a5fa;
        font-size: 16px;
        cursor: pointer;
        pointer-events: auto;
        text-shadow: 0 1px 2px rgba(0,0,0,0.5);
      `;
      el.textContent = '🚢';
      el.title = ship.name;

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        this.popup.show({
          type: 'repair-ship',
          data: ship,
          x: e.clientX - rect.left,
          y: e.clientY - rect.top,
        });
      });

      this.overlays.appendChild(el);
    });
  }

  private renderDataCenters(projection: d3.GeoProjection): void {
    const MIN_GPU_COUNT = 10000;
    
    AI_DATA_CENTERS.filter(dc => (dc.chipCount || 0) >= MIN_GPU_COUNT).forEach(dc => {
      const pos = projection([dc.lon, dc.lat]);
      if (!pos) return;

      const el = document.createElement('div');
      el.className = 'datacenter-marker';
      el.style.cssText = `
        position: absolute;
        left: ${pos[0]}px;
        top: ${pos[1]}px;
        transform: translate(-50%, -50%);
        color: #60a5fa;
        font-size: 16px;
        cursor: pointer;
        pointer-events: auto;
        text-shadow: 0 1px 2px rgba(0,0,0,0.5);
      `;
      el.textContent = '🖥️';
      el.title = dc.name;

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        this.popup.show({
          type: 'datacenter',
          data: dc,
          x: e.clientX - rect.left,
          y: e.clientY - rect.top,
        });
      });

      this.overlays.appendChild(el);
    });
  }

  private renderSpaceports(projection: d3.GeoProjection): void {
    SPACEPORTS.forEach(port => {
      const pos = projection([port.lon, port.lat]);
      if (!pos) return;

      const el = document.createElement('div');
      el.className = 'spaceport-marker';
      el.style.cssText = `
        position: absolute;
        left: ${pos[0]}px;
        top: ${pos[1]}px;
        transform: translate(-50%, -50%);
        color: #f97316;
        font-size: 16px;
        cursor: pointer;
        pointer-events: auto;
        text-shadow: 0 1px 2px rgba(0,0,0,0.5);
      `;
      el.textContent = '🚀';
      el.title = port.name;

      if (this.state.zoom >= 2 && this.state.layers.labels) {
        const label = document.createElement('div');
        label.style.cssText = `
          position: absolute;
          left: 18px;
          top: -4px;
          color: #cbd5e1;
          font-size: 9px;
          white-space: nowrap;
          background: rgba(0,0,0,0.5);
          padding: 2px 4px;
          border-radius: 2px;
        `;
        label.textContent = port.name;
        el.appendChild(label);
      }

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        this.popup.show({
          type: 'spaceport',
          data: port,
          x: e.clientX - rect.left,
          y: e.clientY - rect.top,
        });
      });

      this.overlays.appendChild(el);
    });
  }

  private renderCriticalMinerals(projection: d3.GeoProjection): void {
    CRITICAL_MINERALS.forEach(mine => {
      const pos = projection([mine.lon, mine.lat]);
      if (!pos) return;

      const el = document.createElement('div');
      el.className = 'mineral-marker';
      el.style.cssText = `
        position: absolute;
        left: ${pos[0]}px;
        top: ${pos[1]}px;
        transform: translate(-50%, -50%);
        color: #f59e0b;
        font-size: 16px;
        cursor: pointer;
        pointer-events: auto;
        text-shadow: 0 1px 2px rgba(0,0,0,0.5);
      `;
      
      el.textContent = mine.mineral === 'Lithium' ? '🔋' : 
                       mine.mineral === 'Rare Earths' ? '🧲' : '💎';
      el.title = `${mine.name} (${mine.mineral})`;

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        this.popup.show({
          type: 'mineral',
          data: mine,
          x: e.clientX - rect.left,
          y: e.clientY - rect.top,
        });
      });

      this.overlays.appendChild(el);
    });
  }

  private renderStartupHubs(projection: d3.GeoProjection): void {
    STARTUP_HUBS.forEach(hub => {
      const pos = projection([hub.lon, hub.lat]);
      if (!pos) return;

      const el = document.createElement('div');
      el.className = 'startup-hub-marker';
      el.style.cssText = `
        position: absolute;
        left: ${pos[0]}px;
        top: ${pos[1]}px;
        transform: translate(-50%, -50%);
        color: ${hub.tier === 'mega' ? '#8b5cf6' : hub.tier === 'major' ? '#3b82f6' : '#60a5fa'};
        font-size: 16px;
        cursor: pointer;
        pointer-events: auto;
        text-shadow: 0 1px 2px rgba(0,0,0,0.5);
      `;
      
      el.textContent = hub.tier === 'mega' ? '🦄' : 
                       hub.tier === 'major' ? '🚀' : '💡';
      el.title = hub.name;

      if (this.state.zoom >= 2 || hub.tier === 'mega') {
        const label = document.createElement('div');
        label.style.cssText = `
          position: absolute;
          left: 18px;
          top: -4px;
          color: #cbd5e1;
          font-size: 9px;
          white-space: nowrap;
          background: rgba(0,0,0,0.5);
          padding: 2px 4px;
          border-radius: 2px;
        `;
        label.textContent = hub.name;
        el.appendChild(label);
      }

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        this.popup.show({
          type: 'startupHub',
          data: hub,
          x: e.clientX - rect.left,
          y: e.clientY - rect.top,
        });
      });

      this.overlays.appendChild(el);
    });
  }

  private renderCloudRegions(projection: d3.GeoProjection): void {
    CLOUD_REGIONS.forEach(region => {
      const pos = projection([region.lon, region.lat]);
      if (!pos) return;

      const colors: Record<string, string> = {
        aws: '#f59e0b',
        gcp: '#3b82f6',
        azure: '#8b5cf6',
        cloudflare: '#f97316'
      };

      const el = document.createElement('div');
      el.className = 'cloud-region-marker';
      el.style.cssText = `
        position: absolute;
        left: ${pos[0]}px;
        top: ${pos[1]}px;
        transform: translate(-50%, -50%);
        color: ${colors[region.provider] || '#60a5fa'};
        font-size: 16px;
        cursor: pointer;
        pointer-events: auto;
        text-shadow: 0 1px 2px rgba(0,0,0,0.5);
      `;
      
      const icons: Record<string, string> = {
        aws: '🟠',
        gcp: '🔵',
        azure: '🟣',
        cloudflare: '🟡'
      };
      
      el.textContent = icons[region.provider] || '☁️';
      el.title = `${region.provider.toUpperCase()} - ${region.name}`;

      if (this.state.zoom >= 2) {
        const label = document.createElement('div');
        label.style.cssText = `
          position: absolute;
          left: 18px;
          top: -4px;
          color: #cbd5e1;
          font-size: 9px;
          white-space: nowrap;
          background: rgba(0,0,0,0.5);
          padding: 2px 4px;
          border-radius: 2px;
        `;
        label.textContent = region.provider.toUpperCase();
        el.appendChild(label);
      }

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        this.popup.show({
          type: 'cloudRegion',
          data: region,
          x: e.clientX - rect.left,
          y: e.clientY - rect.top,
        });
      });

      this.overlays.appendChild(el);
    });
  }

  private renderTechHQs(projection: d3.GeoProjection): void {
    const clusters = this.clusterMarkersForHTML(TECH_HQS, projection, 30, hq => hq.city);
    
    clusters.forEach(cluster => {
      if (cluster.count === 0) return;
      
      const el = document.createElement('div');
      el.className = 'tech-hq-marker';
      el.style.cssText = `
        position: absolute;
        left: ${cluster.pos[0]}px;
        top: ${cluster.pos[1]}px;
        transform: translate(-50%, -50%);
        cursor: pointer;
        pointer-events: auto;
      `;

      if (cluster.count > 1) {
        // Cluster
        const marker = document.createElement('div');
        marker.style.cssText = `
          width: 24px;
          height: 24px;
          background: #475569;
          border: 2px solid #94a3b8;
          border-radius: 50%;
          display: flex;
          align-items: center;
          justify-content: center;
          color: white;
          font-size: 10px;
          font-weight: bold;
        `;
        marker.textContent = cluster.count.toString();
        el.appendChild(marker);

        const primaryItem = cluster.items[0] as any;
        el.title = `${primaryItem.city}: ${cluster.items.map((h: any) => h.company).join(', ')}`;
      } else {
        // Single HQ
        const hq = cluster.items[0] as any;
        
        const marker = document.createElement('div');
        marker.style.cssText = `
          font-size: 20px;
          color: ${hq.type === 'faang' ? '#8b5cf6' : 
                   hq.type === 'unicorn' ? '#f59e0b' : '#60a5fa'};
          text-shadow: 0 1px 2px rgba(0,0,0,0.5);
        `;
        marker.textContent = hq.type === 'faang' ? '🏛️' : 
                             hq.type === 'unicorn' ? '🦄' : '🏢';
        el.appendChild(marker);
        el.title = hq.company;

        if (this.state.zoom >= 3) {
          const label = document.createElement('div');
          label.style.cssText = `
            position: absolute;
            left: 22px;
            top: -2px;
            color: #cbd5e1;
            font-size: 9px;
            white-space: nowrap;
            background: rgba(0,0,0,0.5);
            padding: 2px 4px;
            border-radius: 2px;
          `;
          label.textContent = hq.company;
          el.appendChild(label);
        }
      }

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        
        if (cluster.count > 1) {
          const primaryItem = cluster.items[0] as any;
          this.popup.show({
            type: 'techHQCluster',
            data: { 
              items: cluster.items, 
              city: primaryItem.city, 
              country: primaryItem.country 
            },
            x: e.clientX - rect.left,
            y: e.clientY - rect.top,
          });
        } else {
          this.popup.show({
            type: 'techHQ',
            data: cluster.items[0],
            x: e.clientX - rect.left,
            y: e.clientY - rect.top,
          });
        }
      });

      this.overlays.appendChild(el);
    });
  }

  private renderAccelerators(projection: d3.GeoProjection): void {
    ACCELERATORS.forEach(acc => {
      const pos = projection([acc.lon, acc.lat]);
      if (!pos) return;

      const el = document.createElement('div');
      el.className = 'accelerator-marker';
      el.style.cssText = `
        position: absolute;
        left: ${pos[0]}px;
        top: ${pos[1]}px;
        transform: translate(-50%, -50%);
        color: #a855f7;
        font-size: 16px;
        cursor: pointer;
        pointer-events: auto;
        text-shadow: 0 1px 2px rgba(0,0,0,0.5);
      `;
      
      el.textContent = acc.type === 'accelerator' ? '🎯' : 
                       acc.type === 'incubator' ? '🔬' : '🎨';
      el.title = acc.name;

      if (this.state.zoom >= 2) {
        const label = document.createElement('div');
        label.style.cssText = `
          position: absolute;
          left: 18px;
          top: -4px;
          color: #cbd5e1;
          font-size: 9px;
          white-space: nowrap;
          background: rgba(0,0,0,0.5);
          padding: 2px 4px;
          border-radius: 2px;
        `;
        label.textContent = acc.name;
        el.appendChild(label);
      }

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        this.popup.show({
          type: 'accelerator',
          data: acc,
          x: e.clientX - rect.left,
          y: e.clientY - rect.top,
        });
      });

      this.overlays.appendChild(el);
    });
  }

  private renderTechEvents(projection: d3.GeoProjection): void {
    const clusters = this.clusterMarkersForHTML(
      this.techEvents.map(e => ({ ...e, lon: e.lng })), 
      projection, 
      30, 
      e => e.location
    );
    
    clusters.forEach(cluster => {
      if (cluster.count === 0) return;
      
      const el = document.createElement('div');
      el.className = 'tech-event-marker';
      el.style.cssText = `
        position: absolute;
        left: ${cluster.pos[0]}px;
        top: ${cluster.pos[1]}px;
        transform: translate(-50%, -50%);
        cursor: pointer;
        pointer-events: auto;
      `;

      const hasUpcoming = cluster.items.some((e: any) => e.daysUntil <= 14);
      const primaryEvent = cluster.items[0] as any;

      if (cluster.count > 1) {
        const marker = document.createElement('div');
        marker.style.cssText = `
          width: 24px;
          height: 24px;
          background: ${hasUpcoming ? '#f59e0b' : '#475569'};
          border: 2px solid #94a3b8;
          border-radius: 50%;
          display: flex;
          align-items: center;
          justify-content: center;
          color: white;
          font-size: 10px;
          font-weight: bold;
        `;
        marker.textContent = cluster.count.toString();
        el.appendChild(marker);
        el.title = `${primaryEvent.location}: ${cluster.items.map((e: any) => e.title).join(', ')}`;
      } else {
        const marker = document.createElement('div');
        marker.style.cssText = `
          font-size: 20px;
          color: ${hasUpcoming ? '#f59e0b' : '#94a3b8'};
          text-shadow: 0 1px 2px rgba(0,0,0,0.5);
        `;
        marker.textContent = '📅';
        el.appendChild(marker);
        el.title = primaryEvent.title;
      }

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        
        if (cluster.count > 1) {
          this.popup.show({
            type: 'techEventCluster',
            data: { 
              items: cluster.items, 
              location: primaryEvent.location, 
              country: primaryEvent.country 
            },
            x: e.clientX - rect.left,
            y: e.clientY - rect.top,
          });
        } else {
          this.popup.show({
            type: 'techEvent',
            data: primaryEvent,
            x: e.clientX - rect.left,
            y: e.clientY - rect.top,
          });
        }
      });

      this.overlays.appendChild(el);
    });
  }

  private renderStockExchanges(projection: d3.GeoProjection): void {
    STOCK_EXCHANGES.forEach(exchange => {
      const pos = projection([exchange.lon, exchange.lat]);
      if (!pos) return;

      const icon = exchange.tier === 'mega' ? '🏛️' : 
                   exchange.tier === 'major' ? '📊' : '📈';
      
      const el = document.createElement('div');
      el.className = 'stock-exchange-marker';
      el.style.cssText = `
        position: absolute;
        left: ${pos[0]}px;
        top: ${pos[1]}px;
        transform: translate(-50%, -50%);
        color: #60a5fa;
        font-size: ${exchange.tier === 'mega' ? '20px' : '16px'};
        cursor: pointer;
        pointer-events: auto;
        text-shadow: 0 1px 2px rgba(0,0,0,0.5);
        z-index: ${exchange.tier === 'mega' ? 50 : 40};
      `;
      el.textContent = icon;
      el.title = `${exchange.shortName} (${exchange.city})`;

      if (this.state.zoom >= 2 && exchange.tier === 'mega' || this.state.zoom >= 3) {
        const label = document.createElement('div');
        label.style.cssText = `
          position: absolute;
          left: 22px;
          top: -4px;
          color: #cbd5e1;
          font-size: 9px;
          white-space: nowrap;
          background: rgba(0,0,0,0.5);
          padding: 2px 4px;
          border-radius: 2px;
        `;
        label.textContent = exchange.shortName;
        el.appendChild(label);
      }

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        this.popup.show({
          type: 'stockExchange',
          data: exchange,
          x: e.clientX - rect.left,
          y: e.clientY - rect.top,
        });
      });

      this.overlays.appendChild(el);
    });
  }

  private renderFinancialCenters(projection: d3.GeoProjection): void {
    FINANCIAL_CENTERS.forEach(center => {
      const pos = projection([center.lon, center.lat]);
      if (!pos) return;

      const icon = center.type === 'global' ? '💰' : 
                   center.type === 'regional' ? '🏦' : '🏝️';
      
      const el = document.createElement('div');
      el.className = 'financial-center-marker';
      el.style.cssText = `
        position: absolute;
        left: ${pos[0]}px;
        top: ${pos[1]}px;
        transform: translate(-50%, -50%);
        color: #60a5fa;
        font-size: ${center.type === 'global' ? '20px' : '16px'};
        cursor: pointer;
        pointer-events: auto;
        text-shadow: 0 1px 2px rgba(0,0,0,0.5);
        z-index: ${center.type === 'global' ? 45 : 35};
      `;
      el.textContent = icon;
      el.title = `${center.name} Financial Center`;

      if (this.state.zoom >= 2 && center.type === 'global' || this.state.zoom >= 3) {
        const label = document.createElement('div');
        label.style.cssText = `
          position: absolute;
          left: 22px;
          top: -4px;
          color: #cbd5e1;
          font-size: 9px;
          white-space: nowrap;
          background: rgba(0,0,0,0.5);
          padding: 2px 4px;
          border-radius: 2px;
        `;
        label.textContent = center.name;
        el.appendChild(label);
      }

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        this.popup.show({
          type: 'financialCenter',
          data: center,
          x: e.clientX - rect.left,
          y: e.clientY - rect.top,
        });
      });

      this.overlays.appendChild(el);
    });
  }

  private renderCentralBanks(projection: d3.GeoProjection): void {
    CENTRAL_BANKS.forEach(bank => {
      const pos = projection([bank.lon, bank.lat]);
      if (!pos) return;

      const icon = bank.type === 'supranational' ? '🌐' : 
                   bank.type === 'major' ? '🏛️' : '🏦';
      
      const el = document.createElement('div');
      el.className = 'central-bank-marker';
      el.style.cssText = `
        position: absolute;
        left: ${pos[0]}px;
        top: ${pos[1]}px;
        transform: translate(-50%, -50%);
        color: #60a5fa;
        font-size: ${bank.type === 'supranational' ? '20px' : '16px'};
        cursor: pointer;
        pointer-events: auto;
        text-shadow: 0 1px 2px rgba(0,0,0,0.5);
        z-index: ${bank.type === 'supranational' ? 48 : bank.type === 'major' ? 42 : 38};
      `;
      el.textContent = icon;
      el.title = `${bank.shortName} - ${bank.name}`;

      if (this.state.zoom >= 2 && (bank.type === 'major' || bank.type === 'supranational') || this.state.zoom >= 3) {
        const label = document.createElement('div');
        label.style.cssText = `
          position: absolute;
          left: 22px;
          top: -4px;
          color: #cbd5e1;
          font-size: 9px;
          white-space: nowrap;
          background: rgba(0,0,0,0.5);
          padding: 2px 4px;
          border-radius: 2px;
        `;
        label.textContent = bank.shortName;
        el.appendChild(label);
      }

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        this.popup.show({
          type: 'centralBank',
          data: bank,
          x: e.clientX - rect.left,
          y: e.clientY - rect.top,
        });
      });

      this.overlays.appendChild(el);
    });
  }

  private renderCommodityHubs(projection: d3.GeoProjection): void {
    COMMODITY_HUBS.forEach(hub => {
      const pos = projection([hub.lon, hub.lat]);
      if (!pos) return;

      const icon = hub.type === 'exchange' ? '📦' : 
                   hub.type === 'port' ? '🚢' : '⛽';
      
      const el = document.createElement('div');
      el.className = 'commodity-hub-marker';
      el.style.cssText = `
        position: absolute;
        left: ${pos[0]}px;
        top: ${pos[1]}px;
        transform: translate(-50%, -50%);
        color: #60a5fa;
        font-size: 16px;
        cursor: pointer;
        pointer-events: auto;
        text-shadow: 0 1px 2px rgba(0,0,0,0.5);
        z-index: 38;
      `;
      el.textContent = icon;
      el.title = `${hub.name} (${hub.city})`;

      if (this.state.zoom >= 2) {
        const label = document.createElement('div');
        label.style.cssText = `
          position: absolute;
          left: 18px;
          top: -4px;
          color: #cbd5e1;
          font-size: 9px;
          white-space: nowrap;
          background: rgba(0,0,0,0.5);
          padding: 2px 4px;
          border-radius: 2px;
        `;
        label.textContent = hub.name;
        el.appendChild(label);
      }

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        this.popup.show({
          type: 'commodityHub',
          data: hub,
          x: e.clientX - rect.left,
          y: e.clientY - rect.top,
        });
      });

      this.overlays.appendChild(el);
    });
  }

  private renderIranEvents(projection: d3.GeoProjection): void {
    this.iranEvents.forEach(ev => {
      const pos = projection([ev.longitude, ev.latitude]);
      if (!pos) return;

      const size = ev.severity === 'high' ? 10 : ev.severity === 'medium' ? 8 : 6;
      const color = ev.category === 'military' ? '#ef4444' :
                    ev.category === 'politics' ? '#f59e0b' : '#eab308';

      const el = document.createElement('div');
      el.className = 'iran-event-marker';
      el.style.cssText = `
        position: absolute;
        left: ${pos[0]}px;
        top: ${pos[1]}px;
        width: ${size}px;
        height: ${size}px;
        background: ${color};
        border: 1px solid white;
        border-radius: 50%;
        transform: translate(-50%, -50%);
        cursor: pointer;
        pointer-events: auto;
      `;
      el.title = `${ev.title} (${ev.category})`;

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        this.popup.show({
          type: 'iranEvent',
          data: ev,
          x: e.clientX - rect.left,
          y: e.clientY - rect.top,
        });
      });

      this.overlays.appendChild(el);
    });
  }

  private renderProtests(projection: d3.GeoProjection): void {
    const significantProtests = this.protests.filter(
      event => event.eventType === 'riot' || event.severity === 'high'
    );

    const clusters = this.clusterMarkersForHTML(significantProtests, projection, 20, p => p.country);
    
    clusters.forEach(cluster => {
      if (cluster.count === 0) return;
      
      const el = document.createElement('div');
      el.className = 'protest-marker';
      el.style.cssText = `
        position: absolute;
        left: ${cluster.pos[0]}px;
        top: ${cluster.pos[1]}px;
        transform: translate(-50%, -50%);
        cursor: pointer;
        pointer-events: auto;
      `;

      const hasRiot = cluster.items.some((e: any) => e.eventType === 'riot');
      const hasHighSeverity = cluster.items.some((e: any) => e.severity === 'high');

      if (cluster.count > 1) {
        const marker = document.createElement('div');
        marker.style.cssText = `
          width: 24px;
          height: 24px;
          background: ${hasHighSeverity ? '#ef4444' : '#f59e0b'};
          border: 2px solid #f8fafc;
          border-radius: 50%;
          display: flex;
          align-items: center;
          justify-content: center;
          color: white;
          font-size: 10px;
          font-weight: bold;
        `;
        marker.textContent = cluster.count.toString();
        el.appendChild(marker);

        const primaryEvent = cluster.items[0] as any;
        el.title = `${primaryEvent.country}: ${cluster.count} protest events`;
      } else {
        const event = cluster.items[0] as any;
        
        const marker = document.createElement('div');
        marker.style.cssText = `
          font-size: 16px;
          color: ${hasHighSeverity ? '#ef4444' : '#f59e0b'};
          text-shadow: 0 1px 2px rgba(0,0,0,0.5);
        `;
        marker.textContent = hasRiot ? '🔥' : 
                            event.eventType === 'strike' ? '✊' : '📢';
        el.appendChild(marker);
        el.title = `${event.city || event.country} - ${event.eventType}`;
      }

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        
        if (cluster.count > 1) {
          const primaryEvent = cluster.items[0] as any;
          this.popup.show({
            type: 'protestCluster',
            data: { items: cluster.items, country: primaryEvent.country },
            x: e.clientX - rect.left,
            y: e.clientY - rect.top,
          });
        } else {
          this.popup.show({
            type: 'protest',
            data: cluster.items[0],
            x: e.clientX - rect.left,
            y: e.clientY - rect.top,
          });
        }
      });

      this.overlays.appendChild(el);
    });
  }

  private renderFlightDelays(projection: d3.GeoProjection): void {
    this.flightDelays.forEach(delay => {
      const pos = projection([delay.lon, delay.lat]);
      if (!pos) return;

      const color = delay.severity === 'severe' ? '#ef4444' :
                    delay.severity === 'moderate' ? '#f59e0b' : '#94a3b8';

      const el = document.createElement('div');
      el.className = 'flight-delay-marker';
      el.style.cssText = `
        position: absolute;
        left: ${pos[0]}px;
        top: ${pos[1]}px;
        transform: translate(-50%, -50%);
        color: ${color};
        font-size: 16px;
        cursor: pointer;
        pointer-events: auto;
        text-shadow: 0 1px 2px rgba(0,0,0,0.5);
      `;
      
      el.textContent = delay.delayType === 'ground_stop' ? '🛑' : '✈️';
      el.title = `${delay.iata}: ${delay.reason || 'Delay'}`;

      if (this.state.zoom >= 2) {
        const label = document.createElement('div');
        label.style.cssText = `
          position: absolute;
          left: 18px;
          top: -4px;
          color: #cbd5e1;
          font-size: 9px;
          white-space: nowrap;
          background: rgba(0,0,0,0.5);
          padding: 2px 4px;
          border-radius: 2px;
        `;
        label.textContent = `${delay.iata} ${delay.avgDelayMinutes > 0 ? `+${delay.avgDelayMinutes}m` : ''}`;
        el.appendChild(label);
      }

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        this.popup.show({
          type: 'flight',
          data: delay,
          x: e.clientX - rect.left,
          y: e.clientY - rect.top,
        });
      });

      this.overlays.appendChild(el);
    });
  }

  private renderNaturalEvents(projection: d3.GeoProjection): void {
    this.naturalEvents.forEach(event => {
      const pos = projection([event.lon, event.lat]);
      if (!pos) return;

      const el = document.createElement('div');
      el.className = 'nat-event-marker';
      el.style.cssText = `
        position: absolute;
        left: ${pos[0]}px;
        top: ${pos[1]}px;
        transform: translate(-50%, -50%);
        color: #60a5fa;
        font-size: 16px;
        cursor: pointer;
        pointer-events: auto;
        text-shadow: 0 1px 2px rgba(0,0,0,0.5);
      `;
      
      el.textContent = getNaturalEventIcon(event.category);
      el.title = event.title;

      if (this.state.zoom >= 2) {
        const label = document.createElement('div');
        label.style.cssText = `
          position: absolute;
          left: 18px;
          top: -4px;
          color: #cbd5e1;
          font-size: 9px;
          white-space: nowrap;
          background: rgba(0,0,0,0.5);
          padding: 2px 4px;
          border-radius: 2px;
        `;
        label.textContent = event.title.length > 20 ? event.title.slice(0, 20) + '…' : event.title;
        el.appendChild(label);
      }

      if (event.magnitude) {
        const mag = document.createElement('div');
        mag.style.cssText = `
          position: absolute;
          left: 50%;
          top: -14px;
          transform: translateX(-50%);
          color: #f8fafc;
          font-size: 8px;
          background: rgba(0,0,0,0.5);
          padding: 1px 3px;
          border-radius: 2px;
          white-space: nowrap;
        `;
        mag.textContent = `${event.magnitude}${event.magnitudeUnit || ''}`;
        el.appendChild(mag);
      }

      el.addEventListener('click', (e) => {
        e.stopPropagation();
        const rect = this.container.getBoundingClientRect();
        this.popup.show({
          type: 'natEvent',
          data: event,
          x: e.clientX - rect.left,
          y: e.clientY - rect.top,
        });
      });

      this.overlays.appendChild(el);
    });
  }

  private renderFires(projection: d3.GeoProjection): void {
    this.firmsFireData.forEach(fire => {
      const pos = projection([fire.lon, fire.lat]);
      if (!pos) return;

      const color = fire.brightness > 400 ? '#ef4444' : 
                    fire.brightness > 350 ? '#f97316' : '#f59e0b';
      const size = Math.max(3, Math.min(8, (fire.frp || 1) * 0.3));

      const el = document.createElement('div');
      el.className = 'fire-dot';
      el.style.cssText = `
        position: absolute;
        left: ${pos[0]}px;
        top: ${pos[1]}px;
        width: ${size}px;
        height: ${size}px;
        background: ${color};
        border-radius: 50%;
        transform: translate(-50%, -50%);
        pointer-events: none;
      `;

      this.overlays.appendChild(el);
    });
  }

  private clusterMarkersForHTML<T extends { lat: number; lon: number }>(
    items: T[],
    projection: d3.GeoProjection,
    radius = 30,
    getGroupKey?: (item: T) => string
  ): Array<{ items: T[]; count: number; pos: [number, number] }> {
    if (items.length === 0) return [];
    
    if (this.state.zoom >= 3) {
      // Return individual items
      return items
        .filter(item => Number.isFinite(item.lat) && Number.isFinite(item.lon))
        .map(item => {
          const pos = projection([item.lon, item.lat]);
          return pos ? { items: [item], count: 1, pos } : null;
        })
        .filter((c): c is NonNullable<typeof c> => c !== null);
    }

    // Grid-based clustering
    const cellSize = radius * 2;
    const grid = new Map<string, T[]>();

    items.forEach(item => {
      if (!Number.isFinite(item.lat) || !Number.isFinite(item.lon)) return;
      
      const pos = projection([item.lon, item.lat]);
      if (!pos) return;

      const cellX = Math.floor(pos[0] / cellSize);
      const cellY = Math.floor(pos[1] / cellSize);
      let key = `${cellX},${cellY}`;
      
      // If group key provided, include it in clustering key
      if (getGroupKey) {
        key += `|${getGroupKey(item)}`;
      }
      
      if (!grid.has(key)) grid.set(key, []);
      grid.get(key)!.push(item);
    });

    const clusters: Array<{ items: T[]; pos: [number, number] }> = [];

    grid.forEach((cellItems, key) => {
      if (cellItems.length === 0) return;

      // Calculate average position
      let sumX = 0, sumY = 0, count = 0;
      cellItems.forEach(item => {
        const pos = projection([item.lon, item.lat]);
        if (pos) {
          sumX += pos[0];
          sumY += pos[1];
          count++;
        }
      });

      if (count === 0) return;

      const pos: [number, number] = [sumX / count, sumY / count];

      clusters.push({
        items: cellItems,
        pos
      });
    });

    return clusters.map(c => ({
      ...c,
      count: c.items.length
    }));
  }

  private updateCountryFills(): void {
    if (!this.baseLayerGroup || !this.countryFeatures) return;

    const sanctionColors: Record<string, string> = {
      severe: 'rgba(220, 38, 38, 0.3)',
      high: 'rgba(234, 88, 12, 0.2)',
      moderate: 'rgba(250, 204, 21, 0.15)',
    };
    
    const defaultFill = '#1e293b';
    const useSanctions = this.state.layers.sanctions;

    this.baseLayerGroup.selectAll('.country').each(function(datum) {
      const el = d3.select(this);
      const id = datum as { id?: number };
      
      if (!useSanctions) {
        el.attr('fill', defaultFill);
        return;
      }
      
      if (id?.id !== undefined && SANCTIONED_COUNTRIES[id.id]) {
        const level = SANCTIONED_COUNTRIES[id.id];
        el.attr('fill', sanctionColors[level] || defaultFill);
      } else {
        el.attr('fill', defaultFill);
      }
    });
  }

  private getRelatedNews(hotspot: Hotspot): NewsItem[] {
    const conflictTopics = ['gaza', 'ukraine', 'ukrainian', 'russia', 'russian', 'israel', 'israeli', 'iran', 'iranian', 'china', 'chinese', 'taiwan', 'taiwanese', 'korea', 'korean', 'syria', 'syrian'];

    return this.news
      .map(item => {
        const tokens = tokenizeForMatch(item.title);
        const matchedKeywords = findMatchingKeywords(tokens, hotspot.keywords);

        if (matchedKeywords.length === 0) return null;

        const conflictMatches = conflictTopics.filter(t =>
          matchKeyword(tokens, t) && !hotspot.keywords.some(k => k.toLowerCase().includes(t))
        );

        if (conflictMatches.length > 0) {
          const strongLocalMatch = matchedKeywords.some(kw =>
            kw.toLowerCase() === hotspot.name.toLowerCase() ||
            hotspot.agencies?.some(a => matchKeyword(tokens, a))
          );
          if (!strongLocalMatch) return null;
        }

        const score = matchedKeywords.length;
        return { item, score };
      })
      .filter((x): x is { item: NewsItem; score: number } => x !== null)
      .sort((a, b) => b.score - a.score)
      .slice(0, 5)
      .map(x => x.item);
  }

  private getTimeRangeMs(): number {
    const ranges: Record<TimeRange, number> = {
      '1h': 60 * 60 * 1000,
      '6h': 6 * 60 * 60 * 1000,
      '24h': 24 * 60 * 60 * 1000,
      '48h': 48 * 60 * 60 * 1000,
      '7d': 7 * 24 * 60 * 60 * 1000,
      'all': Infinity,
    };
    return ranges[this.state.timeRange];
  }

  private getCableName(cableId: string): string {
    return UNDERSEA_CABLES.find(cable => cable.id === cableId)?.name || cableId;
  }

  private applyTransform(): void {
    this.clampPan();
    
    const zoom = this.state.zoom;
    const width = this.container.clientWidth;
    const height = this.container.clientHeight;

    const centerOffsetX = (width / 2) * (1 - zoom);
    const centerOffsetY = (height / 2) * (1 - zoom);
    const tx = centerOffsetX + this.state.pan.x * zoom;
    const ty = centerOffsetY + this.state.pan.y * zoom;

    this.wrapper.style.transform = `translate(${tx}px, ${ty}px) scale(${zoom})`;
    this.wrapper.style.setProperty('--zoom', String(zoom));

    this.updateZoomLayerVisibility();
    this.emitStateChange();
  }

  private clampPan(): void {
    const zoom = this.state.zoom;
    const width = this.container.clientWidth;
    const height = this.container.clientHeight;

    const maxPanX = (width / 2) * Math.max(1, zoom * 0.8);
    const maxPanY = (height / 2) * Math.max(1, zoom * 0.8);

    this.state.pan.x = Math.max(-maxPanX, Math.min(maxPanX, this.state.pan.x));
    this.state.pan.y = Math.max(-maxPanY, Math.min(maxPanY, this.state.pan.y));
  }

  private updateZoomLayerVisibility(): void {
    const zoom = this.state.zoom;
    
    Object.keys(MapComponent.LAYER_ZOOM_THRESHOLDS).forEach(layer => {
      const thresholds = MapComponent.LAYER_ZOOM_THRESHOLDS[layer as keyof MapLayers];
      if (!thresholds) return;

      const enabled = this.state.layers[layer as keyof MapLayers];
      const override = Boolean(this.layerZoomOverrides[layer as keyof MapLayers]);
      const isVisible = enabled && (override || zoom >= thresholds.minZoom);

      const hiddenAttr = `data-layer-hidden-${layer}`;
      
      if (isVisible) {
        this.wrapper.removeAttribute(hiddenAttr);
      } else {
        this.wrapper.setAttribute(hiddenAttr, 'true');
      }
    });
  }

  private emitStateChange(): void {
    this.onStateChange?.(this.getState());
  }

  public updateHotspotActivity(news: NewsItem[]): void {
    this.news = news;

    this.hotspots.forEach(spot => {
      let score = 0;
      let hasBreaking = false;
      let matchedCount = 0;

      news.forEach(item => {
        const tokens = tokenizeForMatch(item.title);
        const matches = spot.keywords.filter(kw => matchKeyword(tokens, kw));

        if (matches.length > 0) {
          matchedCount++;
          score += matches.length * 2;

          if (item.isAlert) {
            score += 5;
            hasBreaking = true;
          }

          if (item.pubDate) {
            const hoursAgo = (Date.now() - item.pubDate.getTime()) / (1000 * 60 * 60);
            if (hoursAgo < 1) score += 3;
            else if (hoursAgo < 6) score += 2;
            else if (hoursAgo < 24) score += 1;
          }
        }
      });

      spot.hasBreaking = hasBreaking;

      if (hasBreaking || matchedCount >= 4 || score >= 10) {
        spot.level = 'high';
        spot.status = hasBreaking ? 'BREAKING' : 'High activity';
      } else if (matchedCount >= 2 || score >= 4) {
        spot.level = 'elevated';
        spot.status = 'Elevated activity';
      } else if (matchedCount >= 1) {
        spot.level = 'low';
        spot.status = 'Recent mentions';
      } else {
        spot.level = 'low';
        spot.status = 'Monitoring';
      }

      const velocity = matchedCount > 0 ? score / matchedCount : 0;
      updateHotspotEscalation(spot.id, matchedCount, hasBreaking, velocity);
    });

    this.scheduleRender();
  }

  public flashLocation(lat: number, lon: number, durationMs = 2000): void {
    const width = this.container.clientWidth;
    const height = this.container.clientHeight;
    if (!width || !height) return;

    const projection = this.getProjection(width, height);
    const pos = projection([lon, lat]);
    if (!pos) return;

    const flash = document.createElement('div');
    flash.className = 'map-flash';
    flash.style.cssText = `
      position: absolute;
      left: ${pos[0]}px;
      top: ${pos[1]}px;
      width: 40px;
      height: 40px;
      border: 2px solid #f59e0b;
      border-radius: 50%;
      transform: translate(-50%, -50%);
      pointer-events: none;
      animation: flash-pulse ${durationMs}ms ease-out forwards;
    `;
    this.overlays.appendChild(flash);

    setTimeout(() => flash.remove(), durationMs);
  }

  public initEscalationGetters(): void {
    setCIIGetter(getCountryScore);
    setGeoAlertGetter(getAlertsNearLocation);
  }

  public updateMilitaryForEscalation(flights: MilitaryFlight[], vessels: MilitaryVessel[]): void {
    setMilitaryData(flights, vessels);
  }

  public getHotspotDynamicScore(hotspotId: string) {
    return getHotspotEscalation(hotspotId);
  }

  public setView(view: MapView): void {
    this.state.view = view;

    const viewSettings: Record<MapView, { zoom: number; pan: { x: number; y: number } }> = {
      global: { zoom: 1, pan: { x: 0, y: 0 } },
      america: { zoom: 1.8, pan: { x: 180, y: 30 } },
      mena: { zoom: 3.5, pan: { x: -100, y: 50 } },
      eu: { zoom: 2.4, pan: { x: -30, y: 100 } },
      asia: { zoom: 2.0, pan: { x: -320, y: 40 } },
      latam: { zoom: 2.0, pan: { x: 120, y: -100 } },
      africa: { zoom: 2.2, pan: { x: -40, y: -30 } },
      oceania: { zoom: 2.2, pan: { x: -420, y: -100 } },
    };

    const settings = viewSettings[view];
    this.state.zoom = settings.zoom;
    this.state.pan = settings.pan;
    
    this.applyTransform();
    this.scheduleRender();
  }

  private static readonly ASYNC_DATA_LAYERS: Set<keyof MapLayers> = new Set([
    'natural', 'weather', 'outages', 'ais', 'protests', 'flights', 'military', 'techEvents',
  ]);

  public toggleLayer(layer: keyof MapLayers, source: 'user' | 'programmatic' = 'user'): void {
    this.state.layers[layer] = !this.state.layers[layer];
    
    if (this.state.layers[layer]) {
      const thresholds = MapComponent.LAYER_ZOOM_THRESHOLDS[layer];
      if (thresholds && this.state.zoom < thresholds.minZoom) {
        this.layerZoomOverrides[layer] = true;
      } else {
        delete this.layerZoomOverrides[layer];
      }
    } else {
      delete this.layerZoomOverrides[layer];
    }

    // Update button style
    const btn = this.container.querySelector(`[data-layer="${layer}"]`);
    if (btn instanceof HTMLElement) {
      btn.style.background = this.state.layers[layer] ? '#2d5a8c' : '#2d3a4f';
    }

    this.onLayerChange?.(layer, this.state.layers[layer], source);
    this.scheduleRender();
  }

  public setOnLayerChange(callback: (layer: keyof MapLayers, enabled: boolean, source: 'user' | 'programmatic') => void): void {
    this.onLayerChange = callback;
  }

  public setLayerLoading(layer: keyof MapLayers, loading: boolean): void {
    const btn = this.container.querySelector(`.layer-toggle[data-layer="${layer}"]`);
    if (btn instanceof HTMLElement) {
      btn.style.opacity = loading ? '0.5' : '1';
    }
  }

  public setLayerReady(layer: keyof MapLayers, hasData: boolean): void {
    const btn = this.container.querySelector(`.layer-toggle[data-layer="${layer}"]`);
    if (btn instanceof HTMLElement) {
      btn.style.background = this.state.layers[layer] && hasData ? '#2d5a8c' : '#2d3a4f';
    }
  }

  public onStateChanged(callback: (state: MapState) => void): void {
    this.onStateChange = callback;
  }

  public zoomIn(): void {
    this.state.zoom = Math.min(this.state.zoom + 0.5, 10);
    this.applyTransform();
    this.scheduleRender();
  }

  public zoomOut(): void {
    this.state.zoom = Math.max(this.state.zoom - 0.5, 1);
    this.applyTransform();
    this.scheduleRender();
  }

  public reset(): void {
    this.state.zoom = 1;
    this.state.pan = { x: 0, y: 0 };
    this.state.view = 'global';
    this.applyTransform();
    this.scheduleRender();
  }

  public setTimeRange(range: TimeRange): void {
    this.state.timeRange = range;
    this.onTimeRangeChange?.(range);
    
    // Update button styles
    this.container.querySelectorAll('.time-btn').forEach(btn => {
      if (btn instanceof HTMLElement) {
        const range = btn.dataset.range as TimeRange | undefined;
        btn.style.background = range === this.state.timeRange ? '#2d5a8c' : '#2d3a4f';
      }
    });
    
    this.scheduleRender();
  }

  public triggerHotspotClick(id: string): void {
    const hotspot = this.hotspots.find(h => h.id === id);
    if (!hotspot) return;

    const width = this.container.clientWidth;
    const height = this.container.clientHeight;
    const projection = this.getProjection(width, height);
    const pos = projection([hotspot.lon, hotspot.lat]);
    if (!pos) return;

    const relatedNews = this.getRelatedNews(hotspot);
    this.popup.show({
      type: 'hotspot',
      data: hotspot,
      relatedNews,
      x: pos[0],
      y: pos[1],
    });
    this.popup.loadHotspotGdeltContext(hotspot);
    this.onHotspotClick?.(hotspot);
  }

  public triggerConflictClick(id: string): void {
    const conflict = CONFLICT_ZONES.find(c => c.id === id);
    if (!conflict) return;

    const width = this.container.clientWidth;
    const height = this.container.clientHeight;
    const projection = this.getProjection(width, height);
    const pos = projection(conflict.center as [number, number]);
    if (!pos) return;

    this.popup.show({
      type: 'conflict',
      data: conflict,
      x: pos[0],
      y: pos[1],
    });
  }

  public triggerBaseClick(id: string): void {
    const base = MILITARY_BASES.find(b => b.id === id);
    if (!base) return;

    const width = this.container.clientWidth;
    const height = this.container.clientHeight;
    const projection = this.getProjection(width, height);
    const pos = projection([base.lon, base.lat]);
    if (!pos) return;

    this.popup.show({
      type: 'base',
      data: base,
      x: pos[0],
      y: pos[1],
    });
  }

  public triggerPipelineClick(id: string): void {
    const pipeline = PIPELINES.find(p => p.id === id);
    if (!pipeline || pipeline.points.length === 0) return;

    const width = this.container.clientWidth;
    const height = this.container.clientHeight;
    const projection = this.getProjection(width, height);
    const midPoint = pipeline.points[Math.floor(pipeline.points.length / 2)] as [number, number];
    const pos = projection(midPoint);
    if (!pos) return;

    this.popup.show({
      type: 'pipeline',
      data: pipeline,
      x: pos[0],
      y: pos[1],
    });
  }

  public triggerCableClick(id: string): void {
    const cable = UNDERSEA_CABLES.find(c => c.id === id);
    if (!cable || cable.points.length === 0) return;

    const width = this.container.clientWidth;
    const height = this.container.clientHeight;
    const projection = this.getProjection(width, height);
    const midPoint = cable.points[Math.floor(cable.points.length / 2)] as [number, number];
    const pos = projection(midPoint);
    if (!pos) return;

    this.popup.show({
      type: 'cable',
      data: cable,
      x: pos[0],
      y: pos[1],
    });
  }

  public triggerDatacenterClick(id: string): void {
    const dc = AI_DATA_CENTERS.find(d => d.id === id);
    if (!dc) return;

    const width = this.container.clientWidth;
    const height = this.container.clientHeight;
    const projection = this.getProjection(width, height);
    const pos = projection([dc.lon, dc.lat]);
    if (!pos) return;

    this.popup.show({
      type: 'datacenter',
      data: dc,
      x: pos[0],
      y: pos[1],
    });
  }

  public triggerNuclearClick(id: string): void {
    const facility = NUCLEAR_FACILITIES.find(n => n.id === id);
    if (!facility) return;

    const width = this.container.clientWidth;
    const height = this.container.clientHeight;
    const projection = this.getProjection(width, height);
    const pos = projection([facility.lon, facility.lat]);
    if (!pos) return;

    this.popup.show({
      type: 'nuclear',
      data: facility,
      x: pos[0],
      y: pos[1],
    });
  }

  public triggerIrradiatorClick(id: string): void {
    const irradiator = GAMMA_IRRADIATORS.find(i => i.id === id);
    if (!irradiator) return;

    const width = this.container.clientWidth;
    const height = this.container.clientHeight;
    const projection = this.getProjection(width, height);
    const pos = projection([irradiator.lon, irradiator.lat]);
    if (!pos) return;

    this.popup.show({
      type: 'irradiator',
      data: irradiator,
      x: pos[0],
      y: pos[1],
    });
  }

  public enableLayer(layer: keyof MapLayers): void {
    if (!this.state.layers[layer]) {
      this.state.layers[layer] = true;
      const thresholds = MapComponent.LAYER_ZOOM_THRESHOLDS[layer];
      if (thresholds && this.state.zoom < thresholds.minZoom) {
        this.layerZoomOverrides[layer] = true;
      } else {
        delete this.layerZoomOverrides[layer];
      }
      
      const btn = document.querySelector(`[data-layer="${layer}"]`);
      if (btn instanceof HTMLElement) {
        btn.style.background = '#2d5a8c';
      }
      
      this.onLayerChange?.(layer, true, 'programmatic');
      this.scheduleRender();
    }
  }

  public highlightAssets(assets: RelatedAsset[] | null): void {
    Object.keys(this.highlightedAssets).forEach(type => {
      this.highlightedAssets[type as AssetType].clear();
    });

    if (assets) {
      assets.forEach(asset => {
        this.highlightedAssets[asset.type].add(asset.id);
      });
    }

    this.scheduleRender();
  }

  public onHotspotClicked(callback: (hotspot: Hotspot) => void): void {
    this.onHotspotClick = callback;
  }

  public onTimeRangeChanged(callback: (range: TimeRange) => void): void {
    this.onTimeRangeChange = callback;
  }

  public setOnCountryClick(cb: (country: CountryClickPayload) => void): void {
    this.onCountryClick = cb;
  }

  public fitCountry(code: string): void {
    const bbox = getCountryBbox(code);
    if (!bbox) return;
    
    const [minLon, minLat, maxLon, maxLat] = bbox;
    const midLon = (minLon + maxLon) / 2;
    const midLat = (minLat + maxLat) / 2;
    
    const width = this.container.clientWidth;
    const height = this.container.clientHeight;
    const projection = this.getProjection(width, height);
    
    const topLeft = projection([minLon, maxLat]);
    const bottomRight = projection([maxLon, minLat]);
    
    if (!topLeft || !bottomRight) {
      this.state.zoom = 4;
      this.setCenter(midLat, midLon);
      return;
    }
    
    const pxWidth = Math.abs(bottomRight[0] - topLeft[0]);
    const pxHeight = Math.abs(bottomRight[1] - topLeft[1]);
    const padFactor = 0.8;
    
    const zoomX = pxWidth > 0 ? (width * padFactor) / pxWidth : 4;
    const zoomY = pxHeight > 0 ? (height * padFactor) / pxHeight : 4;
    
    this.state.zoom = Math.max(1, Math.min(8, Math.min(zoomX, zoomY)));
    this.setCenter(midLat, midLon);
  }

  public getState(): MapState {
    return { ...this.state };
  }

  public getCenter(): { lat: number; lon: number } | null {
    const width = this.container.clientWidth;
    const height = this.container.clientHeight;
    const projection = this.getProjection(width, height);
    
    if (!projection.invert) return null;
    
    const zoom = this.state.zoom;
    const centerX = width / (2 * zoom) - this.state.pan.x;
    const centerY = height / (2 * zoom) - this.state.pan.y;
    
    const coords = projection.invert([centerX, centerY]);
    if (!coords) return null;
    
    return { lon: coords[0], lat: coords[1] };
  }

  public getTimeRange(): TimeRange {
    return this.state.timeRange;
  }

  public setZoom(zoom: number): void {
    this.state.zoom = Math.max(1, Math.min(10, zoom));
    this.applyTransform();
    this.scheduleRender();
  }

  public setCenter(lat: number, lon: number): void {
    const width = this.container.clientWidth;
    const height = this.container.clientHeight;
    const projection = this.getProjection(width, height);
    const pos = projection([lon, lat]);
    
    if (!pos) return;
    
    this.state.pan = {
      x: width / 2 - pos[0],
      y: height / 2 - pos[1],
    };
    
    this.applyTransform();
    this.scheduleRender();
  }

  public setLayers(layers: MapLayers): void {
    this.state.layers = { ...layers };
    this.scheduleRender();
  }

  public setEarthquakes(earthquakes: Earthquake[]): void {
    this.earthquakes = earthquakes;
    this.scheduleRender();
  }

  public setWeatherAlerts(alerts: WeatherAlert[]): void {
    this.weatherAlerts = alerts;
    this.scheduleRender();
  }

  public setOutages(outages: InternetOutage[]): void {
    this.outages = outages;
    this.scheduleRender();
  }

  public setAisData(disruptions: AisDisruptionEvent[], density: AisDensityZone[]): void {
    this.aisDisruptions = disruptions;
    this.aisDensity = density;
    this.scheduleRender();
  }

  public setCableActivity(advisories: CableAdvisory[], repairShips: RepairShip[]): void {
    this.cableAdvisories = advisories;
    this.repairShips = repairShips;
    this.popup.setCableActivity(advisories, repairShips);
    this.scheduleRender();
  }

  public setCableHealth(healthMap: Record<string, CableHealthRecord>): void {
    this.healthByCableId = healthMap;
    this.scheduleRender();
  }

  public setProtests(events: SocialUnrestEvent[]): void {
    this.protests = events;
    this.scheduleRender();
  }

  public setFlightDelays(delays: AirportDelayAlert[]): void {
    this.flightDelays = delays;
    this.scheduleRender();
  }

  public setMilitaryFlights(flights: MilitaryFlight[], clusters: MilitaryFlightCluster[] = []): void {
    this.militaryFlights = flights;
    this.militaryFlightClusters = clusters;
    this.scheduleRender();
  }

  public setMilitaryVessels(vessels: MilitaryVessel[], clusters: MilitaryVesselCluster[] = []): void {
    this.militaryVessels = vessels;
    this.militaryVesselClusters = clusters;
    this.scheduleRender();
  }

  public setNaturalEvents(events: NaturalEvent[]): void {
    this.naturalEvents = events;
    this.scheduleRender();
  }

  public setFires(fires: Array<{ lat: number; lon: number; brightness: number; frp: number; confidence: number; region: string; acq_date: string; daynight: string }>): void {
    this.firmsFireData = fires;
    this.scheduleRender();
  }

  public setTechEvents(events: TechEventMarker[]): void {
    this.techEvents = events;
    this.scheduleRender();
  }

  public setCyberThreats(_threats: CyberThreat[]): void {
    // SVG fallback doesn't render this layer
  }

  public setIranEvents(events: IranEvent[]): void {
    this.iranEvents = events;
    this.scheduleRender();
  }

  public setNewsLocations(_data: Array<{ lat: number; lon: number; title: string; threatLevel: string; timestamp?: Date }>): void {
    // SVG fallback doesn't render news locations
  }

  public setTechActivity(activities: TechHubActivity[]): void {
    this.techActivities = activities;
    this.scheduleRender();
  }

  public setOnTechHubClick(handler: (hub: TechHubActivity) => void): void {
    this.onTechHubClick = handler;
  }

  public setGeoActivity(activities: GeoHubActivity[]): void {
    this.geoActivities = activities;
    this.scheduleRender();
  }

  public setOnGeoHubClick(handler: (hub: GeoHubActivity) => void): void {
    this.onGeoHubClick = handler;
  }

  public getHotspotLevels(): Record<string, string> {
    const levels: Record<string, string> = {};
    this.hotspots.forEach(spot => {
      levels[spot.name] = spot.level || 'low';
    });
    return levels;
  }

  public setHotspotLevels(levels: Record<string, string>): void {
    this.hotspots.forEach(spot => {
      if (levels[spot.name]) {
        spot.level = levels[spot.name] as 'high' | 'elevated' | 'low';
      }
    });
    this.scheduleRender();
  }
}

// Add CSS animation
const style = document.createElement('style');
style.textContent = `
  @keyframes flash-pulse {
    0% { transform: translate(-50%, -50%) scale(0.5); opacity: 1; }
    100% { transform: translate(-50%, -50%) scale(2); opacity: 0; }
  }
`;
document.head.appendChild(style);
