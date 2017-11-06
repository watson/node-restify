// Copyright 2012 Mark Cavage, Inc.  All rights reserved.

'use strict';

var EventEmitter = require('events').EventEmitter;
var url = require('url');
var util = require('util');
var http = require('http');

var _ = require('lodash');
var assert = require('assert-plus');
var errors = require('restify-errors');
var semver = require('semver');
var FindMyWay = require('find-my-way');
var connect = require('connect');

///--- Globals

// var DEF_CT = 'application/octet-stream';
//
// var BadRequestError = errors.BadRequestError;
// var InternalError = errors.InternalError;
var InvalidArgumentError = errors.InvalidArgumentError;
// var InvalidVersionError = errors.InvalidVersionError;
var MethodNotAllowedError = errors.MethodNotAllowedError;
var ResourceNotFoundError = errors.ResourceNotFoundError;
// var UnsupportedMediaTypeError = errors.UnsupportedMediaTypeError;

///--- API

/**
 * Router class handles mapping of http verbs and a regexp path,
 * to an array of handler functions.
 *
 * @class
 * @public
 * @param  {Object} options - an options object
 * @param  {Bunyan} options.log - Bunyan logger instance
 * @param  {Boolean} [options.strictRouting] - strict routing
 * @param  {String|String[]} [options.contentType] - contentType
 * @param  {String|String[]} [options.versions] - versions
 */
function Router(options) {
    assert.object(options, 'options');
    assert.object(options.log, 'options.log');

    EventEmitter.call(this);

    this.strict = Boolean(options.strictRouting);
    this.log = options.log;
    this.mounts = {};
    this.name = 'RestifyRouter';
    this._afterRoute = options._afterRoute; // or set via server

    // Content type
    this.contentType = options.contentType || [];
    if (!Array.isArray(this.contentType)) {
        this.contentType = [this.contentType];
    }
    assert.arrayOfString(this.contentType, 'options.contentType');

    // Versions
    this.versions = options.versions || options.version || [];
    if (!Array.isArray(this.versions)) {
        this.versions = [this.versions];
    }
    assert.arrayOfString(this.versions, 'options.versions');

    this.versions.forEach(function forEach(v) {
        if (semver.valid(v)) {
            return true;
        }

        throw new InvalidArgumentError('%s is not a valid semver', v);
    });
    this.versions.sort();

    // Internals
    this.mounts = {};
    this.findMyWay = new FindMyWay({
        defaultRoute: this.defaultRoute.bind(this)
    });
}
util.inherits(Router, EventEmitter);

/**
 * Returns true if the router generated a 404 for an options request.
 *
 * TODO: this is relevant for CORS only. Should move this out eventually to a
 * userland middleware? This also seems a little like overreach, as there is no
 * option to opt out of this behavior today.
 *
 * @private
 * @function optionsError
 * @param    {Object}     req - the request object
 * @param    {Object}     res - the response object
 * @returns  {Boolean} is options error
 */
Router.optionsError = function optionsError(req, res) {
    return req.method === 'OPTIONS' && req.url === '*';
};

/**
 * Default route, when no route found
 * Responds with a ResourceNotFoundError error.
 *
 * @private
 * @function defaultRoute
 * @param  {Request} req - request
 * @param  {Response} res - response
 * @returns {undefined} no return value
 */
Router.prototype.defaultRoute = function defaultRoute(req, res) {
    var self = this;

    // Allow CORS
    if (Router.optionsError(req, res)) {
        res.send(200);
        self._afterRoute(null, req, res);
        return;
    }

    // Check for 405 instead of 404
    var allowedMethods = http.METHODS.filter(function some(method) {
        return self.findMyWay.find(method, req.url);
    });

    if (allowedMethods.length) {
        res.methods = allowedMethods;
        res.setHeader('Allow', allowedMethods.join(', '));
        var methodErr = new MethodNotAllowedError(
            '%s is not allowed',
            req.method
        );
        self._afterRoute(methodErr, req, res);
        return;
    }

    // clean up the url in case of potential xss
    // https://github.com/restify/node-restify/issues/1018
    var cleanedUrl = url.parse(req.url).pathname;
    var err = new ResourceNotFoundError('%s does not exist', cleanedUrl);
    self._afterRoute(err, req, res);
};

/**
 * Lookup for route
 *
 * @public
 * @function lookup
 * @param  {Request} req - request
 * @param  {Response} res - response
 * @returns {undefined} no return value
 */
Router.prototype.lookup = function lookup(req, res) {
    this.findMyWay.lookup(req, res);
};

/**
 * Adds a route.
 *
 * @public
 * @function mount
 * @param    {Object} opts - an options object
 * @param    {String} opts.name - name
 * @param    {String} opts.method - method
 * @param    {String} opts.path - path
 * @param    {String[]} [opts.versions] - versions
 * @param    {String} [opts.contentType] - contentType
 * @param    {Function[]} chain - handler chain
 * @returns  {String} returns the route name if creation is successful.
 * @fires ...String#mount
 */
Router.prototype.mount = function mount(opts, chain) {
    var self = this;

    assert.object(opts, 'opts');
    assert.string(opts.method, 'opts.method');
    assert.string(opts.name, 'opts.name');
    assert.arrayOfFunc(chain, 'chain');

    // TODO: revisit (type, versions)
    var app = connect();
    var path = opts.path;

    // Convert RegExp to String for find-my-way
    if (_.isRegExp(path)) {
        path = path.source.replace(/\\/g, '');
    }

    // Route
    var type = opts.contentType || self.contentType;
    var versions = opts.versions || opts.version || self.versions;
    var route = {
        name: opts.name,
        method: opts.method,
        path: path,
        spec: opts,
        types: type,
        versions: versions,
        chain: chain
    };

    route.chain.forEach(function forEach(handler) {
        app.use(handler);
    });

    self.findMyWay.on(route.method, route.path, function onRoute(
        req,
        res,
        params
    ) {
        // Decorate req
        req.params = params;
        req.route = route;

        app(req, res, function afterRouter(err) {
            self._afterRoute(err, req, res);
        });
    });

    // Store route
    self.mounts[route.name] = route;
    self.emit('mount', route.method, route.path, route.type, route.versions);

    return route;
};

/**
 * Unmounts a route.
 *
 * @public
 * @function unmount
 * @param    {String} name - the route name
 * @returns  {String}        the name of the deleted route.
 */
Router.prototype.unmount = function unmount(name) {
    assert.string(name, 'name');

    var route = this.mounts[name];

    if (route) {
        // TODO: revisit
        throw new Error('Unmount is not implemented');
        // this.findMyWay.off(route.method, route.path);
        // delete this.mounts[name];
    }

    return name;
};

/**
 * toString() serialization.
 *
 * @public
 * @function toString
 * @returns  {String} stringified router
 */
Router.prototype.toString = function toString() {
    return this.findMyWay.prettyPrint();
};

/**
 * Return information about the routes registered in the router.
 *
 * @public
 * @returns {object} The routes in the router.
 */
Router.prototype.getDebugInfo = function getDebugInfo() {
    return _.mapValues(this.mounts, function mapValues(route, routeName) {
        return {
            name: route.name,
            method: route.method.toLowerCase(),
            path: route.path,
            versions: route.versions.length > 1 ? route.versions : null
        };
    });
};

module.exports = Router;
